with Ada.Containers;
with Ada.Directories;
with Ada.Environment_Variables;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with Ada.Text_IO;
with Call;                  use Call;
with Configuration;         use Configuration;
with Graphs;
with GPR2.Build;
with GPR2.Build.Actions.Compile.Ada.Analysis;
with GPR2.Build.Actions.Compile.Ada.Global_Gen;
with GPR2.Build.Compilation_Unit;
with GPR2.Build.Compilation_Unit.Maps;
with GPR2.Build.Process_Manager;
with GPR2.Build.Process_Manager.JSON;
with GPR2.Build.Source;
with GPR2.Build.Tree_Db;
with GPR2.Path_Name;
with GPR2.Project.View;
with GNAT.OS_Lib;
with GNAT.Strings;          use GNAT.Strings;
with GNATCOLL.JSON;         use GNATCOLL.JSON;
with GNATCOLL.Utils;        use GNATCOLL.Utils;
with GNATCOLL.VFS;          use GNATCOLL.VFS;
with Named_Semaphores;      use Named_Semaphores;
with String_Utils;          use String_Utils;
with VC_Kinds;              use VC_Kinds;

package body Gnatprove_Build is

   function Spawn_VC_Server_And_Semaphore
     (Tree : Project.Tree.Object) return GNAT.OS_Lib.Process_Id;
   --  Spawn the VC server of Why3 and create the semaphore used for gnatwhy3
   --  processes. Also set the environment variables used by the binaries that
   --  access these resources.

   function Non_Blocking_Spawn
     (Command : String; Arguments : String_Lists.List)
      return GNAT.OS_Lib.Process_Id;
   --  Spawn a process in a non-blocking way

   procedure Write_Why3_Conf_File (Obj_Dir : String);
   --  Write the Why3 conf file to process prover configuration

   function Create_Object_Path_File (Tree : Project.Tree.Object) return String;
   --  Create the object path file which contains the object dirs
   --  of all projects and is passed to gnat2why (second phase) via -gnateO
   --  switch. The result of this function is the file name of the temp file.
   --  The caller is responsible for cleanup (deleting) this file.

   subtype Unit_Set is GPR2.Build.Compilation_Unit.Maps.Map;

   type Edge_Colour_T is (No_Colour);

   function Hash_For_Graph
     (Key : GPR2.Build.Compilation_Unit.Object) return Ada.Containers.Hash_Type
   is (Hash (Key.Name));

   function Test_Key
     (Left, Right : GPR2.Build.Compilation_Unit.Object) return Boolean
   is (Left.Name = Right.Name);

   package Unit_Graphs is new
     Graphs
       (Vertex_Key   => GPR2.Build.Compilation_Unit.Object,
        Edge_Colours => Edge_Colour_T,
        Null_Key     => GPR2.Build.Compilation_Unit.Undefined,
        Key_Hash     => Hash_For_Graph,
        Test_Key     => Test_Key);

   Unit_Dependency_Graph : Unit_Graphs.Graph := Unit_Graphs.Create;

   procedure Full_Deps (Tree : Project.Tree.Object);
   --  Compute full dependencies for all units using the Graphs module

   -----------------------------
   -- Create_Object_Path_File --
   -----------------------------

   function Create_Object_Path_File (Tree : Project.Tree.Object) return String
   is
      use Ada.Text_IO;
      FT   : File_Type;
      Name : constant String :=
        Ada.Directories.Compose
          (Configuration.Artifact_Dir (Tree).Virtual_File.Display_Full_Name,
           "obj_path.tmp");
   begin
      --  ??? possibly this needs to change for aggregate projects - one file
      --  per aggregate
      --  ??? Do we need to add the Library_Dir for library projects
      --  instead of the object dir?
      Create (FT, Name => Name);
      for Prj of Tree.Ordered_Views loop
         if Prj.Kind in With_Object_Dir_Kind then
            if Prj.Is_Library then
               declare
                  Lib_Dir    : Virtual_File renames
                    Prj.Library_Ali_Directory.Virtual_File;
                  --  ??? for some reason the subdir is missing for externally
                  --  built projects
                  Target_Dir : constant Virtual_File :=
                    (if Prj.Is_Externally_Built
                     then Lib_Dir / Configuration.Phase2_Subdir
                     else Lib_Dir);
               begin
                  Put (FT, Target_Dir.Display_Full_Name & ASCII.LF);
               end;
            else
               Put
                 (FT,
                  Prj.Object_Directory.Virtual_File.Display_Full_Name
                  & ASCII.LF);
            end if;
         end if;
      end loop;
      Close (FT);
      return Name;
   end Create_Object_Path_File;

   -----------------------------
   -- Flow_Analysis_And_Proof --
   -----------------------------
   procedure Flow_Analysis_And_Proof
     (Tree : Project.Tree.Object; Status : out Integer)
   is
      Process_M : GPR2.Build.Process_Manager.JSON.Object;
      Exec_Opts : GPR2.Build.Process_Manager.PM_Options;
      Id        : GNAT.OS_Lib.Process_Id := GNAT.OS_Lib.Invalid_Pid;
      use type GPR2.Build.Process_Manager.Execution_Status;
      use type GNAT.OS_Lib.Process_Id;

      procedure Cleanup;
      --  Delete temp files, close semaphore, kill VC server

      procedure Insert_Actions
        (Main_Files : Unit_Set; Selected_Files : Unit_Set);
      --  Build the DAG of actions for global gen and analysis

      Object_Path_File : constant String := Create_Object_Path_File (Tree);

      -------------
      -- Cleanup --
      -------------

      procedure Cleanup is
      begin
         if Id /= GNAT.OS_Lib.Invalid_Pid then
            GNAT.OS_Lib.Kill (Id, Hard_Kill => False);
            declare
               Pid    : GNAT.OS_Lib.Process_Id;
               Unused : Boolean;
            begin
               --  Wait for the killed process to gently terminate and for
               --  the underlying resources to be reclaimed.

               GNAT.OS_Lib.Wait_Process (Pid, Unused);
               pragma Assert (Pid = Id);
            end;
         end if;
         if Use_Semaphores and then Configuration.Mode in GPM_All | GPM_Prove
         then
            Close (Why3_Semaphore);
            Delete (Semaphore_Name);
         end if;
         if not Configuration.Debug then
            Tree.Artifacts_Database.Clear_Temp_Files;
            for File of Opt_File_Set loop
               Ada.Directories.Delete_File (File);
            end loop;
            Ada.Directories.Delete_File (Object_Path_File);
         end if;
      exception
         --  Don't crash when there are problems during cleanup
         when others =>
            null;
      end Cleanup;

      --------------------
      -- Insert_Actions --
      --------------------

      procedure Insert_Actions
        (Main_Files : Unit_Set; Selected_Files : Unit_Set)
      is
         To_Analyse    : Unit_Set;
         To_Global_Gen : Unit_Set;

         procedure Analyse_All_Units;
         --  Helper to add all units of the project tree to the To_Analyse set

         -----------------------
         -- Analyse_All_Units --
         -----------------------

         procedure Analyse_All_Units is
         begin
            for Prj of Tree.Ordered_Views loop
               for Unit of Prj.Own_Units loop
                  To_Analyse.Include (Unit.Name, Unit);
               end loop;
            end loop;
         end Analyse_All_Units;

         use type GPR2.Project.View.Object;
      begin
         if CL_Switches.UU and then Selected_Files.Is_Empty then
            Analyse_All_Units;
         elsif not Selected_Files.Is_Empty then
            for C in Selected_Files.Iterate loop
               To_Analyse.Include (C.Key, C.Element);
            end loop;
         elsif not Main_Files.Is_Empty then
            for C in Main_Files.Iterate loop
               To_Analyse.Include (C.Key, C.Element);
               --  Add all dependencies using the graph's out-neighbors
               declare
                  V_Id       : constant Unit_Graphs.Vertex_Id :=
                    Unit_Graphs.Get_Vertex (Unit_Dependency_Graph, C.Element);
                  Neighbours : constant Unit_Graphs.Vertex_Collection_T :=
                    Unit_Graphs.Get_Collection
                      (Unit_Dependency_Graph,
                       V_Id,
                       Unit_Graphs.Out_Neighbours);
               begin
                  for Dep_V_Id of Neighbours loop
                     declare
                        Dep : constant GPR2.Build.Compilation_Unit.Object :=
                          Unit_Graphs.Get_Key
                            (Unit_Dependency_Graph, Dep_V_Id);
                     begin
                        To_Analyse.Include (Dep.Name, Dep);
                     end;
                  end loop;
               end;
            end loop;
         else
            Analyse_All_Units;
         end if;

         --  all units to be analyzed and all their deps need global gen
         for C in To_Analyse.Iterate loop
            To_Global_Gen.Include (C.Key, C.Element);
            --  Add all dependencies using the graph's out-neighbors
            declare
               V_Id       : constant Unit_Graphs.Vertex_Id :=
                 Unit_Graphs.Get_Vertex (Unit_Dependency_Graph, C.Element);
               Neighbours : constant Unit_Graphs.Vertex_Collection_T :=
                 Unit_Graphs.Get_Collection
                   (Unit_Dependency_Graph, V_Id, Unit_Graphs.Out_Neighbours);
            begin
               for Dep_V_Id of Neighbours loop
                  declare
                     Dep : constant GPR2.Build.Compilation_Unit.Object :=
                       Unit_Graphs.Get_Key (Unit_Dependency_Graph, Dep_V_Id);
                  begin
                     To_Global_Gen.Include (Dep.Name, Dep);
                  end;
               end loop;
            end;
         end loop;

         for C in To_Global_Gen.Iterate loop
            declare
               Owning : constant GPR2.Project.View.Object :=
                 C.Element.Owning_View;
            begin
               if (not CL_Switches.No_Subprojects
                   or else Owning = Tree.Root_Project)
                 and then not Owning.Is_Externally_Built
               then
                  declare
                     GG_Act : GPR2.Build.Actions.Compile.Ada.Global_Gen.Object;
                  begin
                     GG_Act.Initialize (C.Element);
                     if not Tree.Artifacts_Database.Add_Action (GG_Act) then
                        Ada.Text_IO.Put_Line
                          ("Error adding Global_Gen action for unit "
                           & String (C.Element.Name));
                     end if;
                  end;
               end if;
            end;
         end loop;
         for C in To_Analyse.Iterate loop
            declare
               Owning : constant GPR2.Project.View.Object :=
                 C.Element.Owning_View;
            begin
               if (not CL_Switches.No_Subprojects
                   or else Owning = Tree.Root_Project)
                 and then not Owning.Is_Externally_Built
               then
                  declare
                     Analysis_Act :
                       GPR2.Build.Actions.Compile.Ada.Analysis.Object;
                     Unit_Deps    : Unit_Set;
                  begin
                     --  Build the set of units for which we will need the .ali
                     --  files
                     declare
                        V_Id       : constant Unit_Graphs.Vertex_Id :=
                          Unit_Graphs.Get_Vertex
                            (Unit_Dependency_Graph, C.Element);
                        Neighbours :
                          constant Unit_Graphs.Vertex_Collection_T :=
                            Unit_Graphs.Get_Collection
                              (Unit_Dependency_Graph,
                               V_Id,
                               Unit_Graphs.Out_Neighbours);
                     begin
                        for Dep_V_Id of Neighbours loop
                           declare
                              Dep :
                                constant GPR2.Build.Compilation_Unit.Object :=
                                  Unit_Graphs.Get_Key
                                    (Unit_Dependency_Graph, Dep_V_Id);
                           begin
                              Unit_Deps.Include (Dep.Name, Dep);
                           end;
                        end loop;
                     end;

                     Analysis_Act.Initialize
                       (C.Element, Object_Path_File, Unit_Deps);
                     if not Tree.Artifacts_Database.Add_Action (Analysis_Act)
                     then
                        Ada.Text_IO.Put_Line
                          ("Error adding Analysis action for unit "
                           & String (C.Element.Name));
                     end if;
                  end;
               end if;
            end;
         end loop;

      end Insert_Actions;

   begin
      Process_M.Set_JSON_File
        (Path_Name.Compose
           (Configuration.Artifact_Dir (Tree), "gnatprove_build.json"));
      if Configuration.Mode in GPM_All | GPM_Prove then
         Id := Spawn_VC_Server_And_Semaphore (Tree);
      end if;
      if Configuration.Debug then
         Exec_Opts.Keep_Temp_Files := True;
      end if;
      if CL_Switches.K then
         Exec_Opts.Stop_On_Fail := False;
      end if;
      if CL_Switches.F then
         Exec_Opts.Force := True;
      end if;

      --  ??? set Exec.Jobs based on CL_Switches.Parallel
      --  This currently causes a regression in K622-001__multisource
      Exec_Opts.Jobs := Configuration.Parallel;

      --  ??? it seems correct to write this file only once, but will why3
      --  processes of units of non-root projects find it?
      Write_Why3_Conf_File
        (Configuration.Artifact_Dir (Tree).Virtual_File.Display_Full_Name);

      Full_Deps (Tree);

      --  decide which units to analyze
      declare
         Main_Files     : Unit_Set;
         Selected_Files : Unit_Set;
      begin
         if not Configuration.Unit_List.Is_Empty then
            if Configuration.Only_Given or else CL_Switches.UU then
               Selected_Files := Configuration.Unit_List;
            else
               Main_Files := Configuration.Unit_List;
            end if;
         else
            for NRP of Tree.Namespace_Root_Projects loop
               for Main of NRP.Mains loop
                  declare
                     Source : constant GPR2.Build.Source.Object :=
                       Main.View.Visible_Source (Main.Source);
                     Unit   : Build.Compilation_Unit.Object;
                  begin
                     if Source.Language = Ada_Language then
                        Unit :=
                          Main.View.Own_Unit
                            (Source.Units.Element (Main.Index).Name);
                        if Unit.Is_Defined then
                           Main_Files.Include (Unit.Name, Unit);
                        end if;
                     end if;
                  end;
               end loop;
            end loop;
         end if;
         Insert_Actions (Main_Files, Selected_Files);
      end;

      if Tree.Artifacts_Database.Execute (Process_M, Exec_Opts)
        /= GPR2.Build.Process_Manager.Success
      then
         Status := 1;
      else
         Status := 0;
      end if;

      --  TODO delete why3 conf files
      --  TODO in debug mode, output should not be buffered

      Cleanup;
   exception
      when others =>
         Cleanup;
         raise;

   end Flow_Analysis_And_Proof;

   procedure Full_Deps (Tree : Project.Tree.Object) is
      All_Units : Unit_Set;
   begin
      --  Clear previous state
      Unit_Dependency_Graph := Unit_Graphs.Create;

      --  Collect all units and add them as vertices to the graph
      for Prj of Tree.Ordered_Views loop
         for Unit of Prj.Own_Units loop
            if Unit.Is_Defined then
               All_Units.Include (Unit.Name, Unit);
               Unit_Graphs.Include_Vertex (Unit_Dependency_Graph, Unit);
            end if;
         end loop;
      end loop;

      --  Add edges based on Known_Dependencies
      for C in All_Units.Iterate loop
         declare
            U : constant Build.Compilation_Unit.Object := C.Element;
         begin
            for Dep_Name of U.Known_Dependencies loop
               if All_Units.Contains (Dep_Name) then
                  Unit_Graphs.Add_Edge
                    (Unit_Dependency_Graph, U, All_Units.Element (Dep_Name));
               end if;
            end loop;
         end;
      end loop;

      --  Compute transitive closure using the Close method
      Unit_Graphs.Close (Unit_Dependency_Graph);

   end Full_Deps;

   ------------------------
   -- Non_Blocking_Spawn --
   ------------------------

   function Non_Blocking_Spawn
     (Command : String; Arguments : String_Lists.List)
      return GNAT.OS_Lib.Process_Id
   is
      Executable : GNAT.OS_Lib.String_Access :=
        GNAT.OS_Lib.Locate_Exec_On_Path (Command);
      Args       : GNAT.OS_Lib.Argument_List :=
        Argument_List_Of_String_List (Arguments);
      Proc       : GNAT.OS_Lib.Process_Id;
   begin
      if Executable = null then
         Ada.Text_IO.Put_Line ("Could not find executable " & Command);
         GNAT.OS_Lib.OS_Exit (1);
      end if;
      if Debug then
         Ada.Text_IO.Put (Executable.all);
         for Arg of Args loop
            Ada.Text_IO.Put (" " & Arg.all);
         end loop;
         Ada.Text_IO.New_Line;
      end if;
      Proc := GNAT.OS_Lib.Non_Blocking_Spawn (Executable.all, Args);
      Free (Args);
      Free (Executable);
      return Proc;
   end Non_Blocking_Spawn;

   ---------------------
   -- Spawn_VC_Server --
   ---------------------

   function Spawn_VC_Server_And_Semaphore
     (Tree : Project.Tree.Object) return GNAT.OS_Lib.Process_Id
   is
      Args : String_Lists.List;
      Cur  : constant String := Ada.Directories.Current_Directory;
      Id   : GNAT.OS_Lib.Process_Id := GNAT.OS_Lib.Invalid_Pid;
   begin
      if CL_Switches.Why3_Server = null
        or else CL_Switches.Why3_Server.all = ""
      then
         Ada.Directories.Set_Directory
           (Artifact_Dir (Tree).Virtual_File.Display_Full_Name);
         Args.Append ("-j");
         Args.Append (Image (Parallel, 1));
         Args.Append ("--socket");
         Args.Append (Socket_Name.all);
         if Debug then
            Args.Append ("--logging");
         end if;
         Id := Non_Blocking_Spawn ("why3server", Args);
         Ada.Directories.Set_Directory (Cur);
         Ada.Environment_Variables.Set ("GNATPROVE_SOCKET", Socket_Name.all);
      else
         Ada.Environment_Variables.Set
           ("GNATPROVE_SOCKET", CL_Switches.Why3_Server.all);
      end if;
      if Use_Semaphores then
         Delete (Semaphore_Name);
         Create (Semaphore_Name, Max_Why3_Processes, Why3_Semaphore);
         Ada.Environment_Variables.Set ("GNATPROVE_SEMAPHORE", Semaphore_Name);
      end if;
      return Id;
   end Spawn_VC_Server_And_Semaphore;

   --------------------------
   -- Write_Why3_Conf_File --
   --------------------------

   procedure Write_Why3_Conf_File (Obj_Dir : String) is
      use Ada.Text_IO;

      --  Here we read the "gnatprove.conf" file and generate from it
      --  the "why3.conf" file. This comment defines the structure of the
      --  "gnatprove.conf" file.
      --  Note that we leave many fields uncommented here because they map
      --  directly to why3 fields.
      --
      --  gnatprove.conf =
      --    { magic    : int,
      --      memlimit : int,
      --      provers  : list prover,
      --      editors  : list editor
      --    }
      --
      --  "magic" and "memlimit" map directly to the entries in Why3.conf in
      --  the [main] section.
      --
      --  prover =
      --    { executable : string,
      --      args       : list string,
      --      args_steps : list string,
      --      driver     : string,
      --      name       : string,
      --      shortcut   : string,
      --      version    : string
      --    }
      --
      --    "driver", "name", "shortcut", "version" map directly to why3.conf
      --    keys for a prover. "executable" is just the name of the binary to
      --    be run. "args" are all the arguments for a run without a step
      --    limit. "args_steps" are the *extra* arguments that need to be
      --    provided for a steps limit to be active.
      --
      --  editor =
      --    { title      : string,
      --      name       : string,
      --      executable : string,
      --      args       : list string
      --    }
      --
      --  "title" maps to the name of the editor used in the title of the
      --  section, e.g. for "[editor coqide]" the title would be "coqide".
      --  "name" maps to the why3.conf key. "executable" is just the name of
      --  the binary, and "args" the arguments that need to be provided.

      File : File_Type;

      procedure Start_Section (Name : String);
      --  Start a section in the why3.conf file

      procedure Set_Key_Value (Key, Value : String);
      --  Write a line 'key = "value"' to the why3.conf file

      procedure Set_Key_Value_Int (Key : String; Value : Integer);
      --  Same, but for Integers. We do not use overloading, because in
      --  connection with the overloading of JSON API, this will require type
      --  annotations.

      procedure Set_Key_Value_Bool (Key : String; Value : Boolean);
      --  Same, but for Booleans.

      procedure Write_Prover_Config (Prover : JSON_Value);
      --  Write the config of a prover

      procedure Write_Editor_Config (Editor : JSON_Value);
      --  Write the config of an editor

      function Build_Prover_Command
        (Prover : JSON_Value; Args_Step : Boolean) return String;
      --  Given a prover configuration in JSON, construct the prover command
      --  for why3.conf (with or without steps depending on Args_Step value).

      function Build_Executable (Exec : String) return String;
      --  Build the part of a command that corresponds to the executable. Takes
      --  into account Benchmark mode.

      ----------------------
      -- Build_Executable --
      ----------------------

      function Build_Executable (Exec : String) return String is

         function Add_Memcached_Wrapper (Cmd : String) return String;
         function Add_Benchmark_Prefix (Cmd : String) return String;

         --------------------------
         -- Add_Benchmark_Prefix --
         --------------------------

         function Add_Benchmark_Prefix (Cmd : String) return String is
         begin
            if CL_Switches.Benchmark then
               return "fake_" & Cmd;
            else
               return Cmd;
            end if;
         end Add_Benchmark_Prefix;

         ---------------------------
         -- Add_Memcached_Wrapper --
         ---------------------------

         function Add_Memcached_Wrapper (Cmd : String) return String is
         begin
            if CL_Switches.Memcached_Server /= null
              and then CL_Switches.Memcached_Server.all /= ""
            then
               return
                 "spark_memcached_wrapper %t "
                 & CL_Switches.Memcached_Server.all
                 & " "
                 & Cmd;
            else
               return Cmd;
            end if;
         end Add_Memcached_Wrapper;

         --  Start of processing for Build_Executable

      begin
         return Add_Memcached_Wrapper (Add_Benchmark_Prefix (Exec));
      end Build_Executable;

      --------------------------
      -- Build_Prover_Command --
      --------------------------

      function Build_Prover_Command
        (Prover : JSON_Value; Args_Step : Boolean) return String
      is
         Command  : Unbounded_String;
         Args     : constant JSON_Array := Get (Get (Prover, "args"));
         Args_Add : constant JSON_Array :=
           (if Args_Step
            then Get (Get (Prover, "args_steps"))
            else Get (Get (Prover, "args_time")));
      begin
         Append
           (Command,
            Build_Executable (String'(Get (Get (Prover, "executable")))));
         for Index in 1 .. Length (Args_Add) loop
            Append (Command, " " & String'(Get (Get (Args_Add, Index))));
         end loop;
         for Index in 1 .. Length (Args) loop
            Append (Command, " " & String'(Get (Get (Args, Index))));
         end loop;
         return To_String (Command);
      end Build_Prover_Command;

      -------------------
      -- Set_Key_Value --
      -------------------

      procedure Set_Key_Value (Key, Value : String) is
      begin
         Put_Line (File, Key & " = " & '"' & Value & '"');
      end Set_Key_Value;

      ------------------------
      -- Set_Key_Value_Bool --
      ------------------------

      procedure Set_Key_Value_Bool (Key : String; Value : Boolean) is
      begin
         Put_Line (File, Key & " = " & (if Value then "true" else "false"));
      end Set_Key_Value_Bool;

      -----------------------
      -- Set_Key_Value_Int --
      -----------------------

      procedure Set_Key_Value_Int (Key : String; Value : Integer) is
      begin
         Put_Line (File, Key & " = " & Integer'Image (Value));
      end Set_Key_Value_Int;

      -------------------
      -- Start_Section --
      -------------------

      procedure Start_Section (Name : String) is
      begin
         Put_Line (File, "[" & Name & "]");
      end Start_Section;

      -------------------------
      -- Write_Editor_Config --
      -------------------------

      procedure Write_Editor_Config (Editor : JSON_Value) is
      begin
         Start_Section ("editor " & Get (Get (Editor, "title")));
         Set_Key_Value ("name", Get (Get (Editor, "name")));
         Set_Key_Value
           ("command", Build_Prover_Command (Editor, Args_Step => False));
      end Write_Editor_Config;

      -------------------------
      -- Write_Prover_Config --
      -------------------------

      procedure Write_Prover_Config (Prover : JSON_Value) is
      begin
         Start_Section ("prover");
         Set_Key_Value
           ("command", Build_Prover_Command (Prover, Args_Step => False));
         if Has_Field (Prover, "args_steps") then
            Set_Key_Value
              ("command_steps",
               Build_Prover_Command (Prover, Args_Step => True));
         end if;
         Set_Key_Value ("driver", Get (Get (Prover, "driver")));
         Set_Key_Value ("name", Get (Get (Prover, "name")));
         Set_Key_Value ("shortcut", Get (Get (Prover, "shortcut")));
         Set_Key_Value ("version", Get (Get (Prover, "version")));
         if Has_Field (Prover, "interactive") then
            Set_Key_Value_Bool
              ("interactive", Get (Get (Prover, "interactive")));
         end if;
         if Has_Field (Prover, "editor") then
            Set_Key_Value ("editor", Get (Get (Prover, "editor")));
         end if;
         if Has_Field (Prover, "in_place") then
            Set_Key_Value_Bool ("in_place", Get (Get (Prover, "in_place")));
         end if;

      end Write_Prover_Config;

      Config : constant JSON_Value :=
        Read_File_Into_JSON (SPARK_Install.Gnatprove_Conf);

      Editors  : constant JSON_Array := Get (Get (Config, "editors"));
      Provers  : constant JSON_Array := Get (Get (Config, "provers"));
      Filename : constant String :=
        Ada.Directories.Compose (Obj_Dir, "why3.conf");

      --  Start of processing for Write_Why3_Conf_File

   begin
      Create (File, Out_File, Filename);
      Start_Section ("main");
      Set_Key_Value_Int ("magic", Get (Get (Config, "magic")));
      Set_Key_Value_Int ("memlimit", Get (Get (Config, "memlimit")));
      for Index in 1 .. Length (Editors) loop
         Write_Editor_Config (Get (Editors, Index));
      end loop;
      for Index in 1 .. Length (Provers) loop
         Write_Prover_Config (Get (Provers, Index));
      end loop;
      Close (File);
   end Write_Why3_Conf_File;

end Gnatprove_Build;
