------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                            G N A T P R O V E                             --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2019, AdaCore                     --
--                Copyright (C) 2014-2019, Altran UK Limited                --
--                                                                          --
-- gnatprove is  free  software;  you can redistribute it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnatprove is distributed  in the hope that  it will be useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General Public License  distributed with  gnatprove;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnatprove is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

--  This program (gnatprove) is the command line interface of the SPARK 2014
--  tools. It works in three steps:
--
--  1) Compute_ALI_Information
--     This step generates, for all relevant units, the ALI files, which
--     contain the computed effects for all subprograms and packages.
--  2) Flow_Analysis_And_Proof
--     This step does all the SPARK analyses: flow analysis and proof. The tool
--     "gnat2why" is called on all units, translates the SPARK code to Why3
--     and calls gnatwhy3 to prove the generated VCs.
--  3) Call SPARK_Report. The previous steps have generated extra information,
--     which is read in by the spark_report tool, and aggregated to a report.
--     See the documentation of spark_report.adb for the details.

--  --------------------------
--  -- Incremental Analysis --
--  --------------------------

--  GNATprove wants to achieve minimal work when rerun after a few changes to
--  the project, while keeping the analysis correct. Two different mechanisms
--  are used to achieve this:
--    - GPRbuild facilities for incremental compilation
--    - Why3 session mechanism

--  GPRbuild is capable of only recompiling files that actually need
--  recompiling. As we use GPRbuild with gnat2why as a special 'compiler',
--  there is nothing special to do to benefit from this, except that its
--  dependency model is slightly different. This is taken into account by:
--    . specifying the mode "ALI_Closure" as Dependency_Kind in the first phase
--      of GNATprove
--    . calling GPRbuild with the "-s" switch to take into account changes of
--      compilation options.
--    . calling GPRbuild with the "--complete-output" switch to replay the
--      stored output (both on stdout and stderr) of a previous run on some
--      unit, when this unit output is up-to-date. This allows to get the same
--      messages for warnings and checks when calling GNATprove multiple times
--      on the same units, even when sources have not changed so analysis is
--      not done on these units.

with Ada.Command_Line;
with Ada.Containers;
with Ada.Directories;            use Ada.Directories;
with Ada.Environment_Variables;
with Ada.Strings.Unbounded;
with Ada.Text_IO;                use Ada.Text_IO;
with Call;                       use Call;
with Configuration;              use Configuration;
with GNAT.Expect;                use GNAT.Expect;
with GNAT.OS_Lib;
with GNAT.Strings;               use GNAT.Strings;
with Gnat2Why_Opts.Writing;
with GNATCOLL.JSON;              use GNATCOLL.JSON;
with GNATCOLL.Projects;          use GNATCOLL.Projects;
with GNATCOLL.VFS;               use GNATCOLL.VFS;
with GNATCOLL.Utils;             use GNATCOLL.Utils;
with String_Utils;               use String_Utils;

procedure Gnatprove with SPARK_Mode is

   type Gnatprove_Step is (GS_ALI, GS_CodePeer, GS_Gnat2Why);

   type Plan_Type is array (Positive range <>) of Gnatprove_Step;

   procedure Call_Gprbuild
     (Project_File      : String;
      Proj              : Project_Tree;
      DB_Dir            : String;
      Translation_Phase : Boolean;
      Args              : in out String_Lists.List;
      Status            : out Integer);
   --  Call gprbuild with the given arguments. DB_Dir is the directory
   --  which contains the information to configure gprbuild correctly.

   procedure Compute_ALI_Information
     (Project_File : String;
      Proj         : Project_Tree;
      Status       : out Integer);
   --  Compute ALI information for all source units, using gprbuild

   procedure Execute_Step
     (Plan         : Plan_Type;
      Step         : Positive;
      Project_File : String;
      Proj         : Project_Tree);

   procedure Copy_ALI_Files (Proj : Project_Tree);
   --  To be called between phase 1 and phase2. Copies the ALI files from the
   --  subdir of the first phase to the one for the second phase.

   procedure Generate_SPARK_Report
     (Proj     : Project_Type;
      Obj_Dir  : String;
      Obj_Path : File_Array);
   --  Generate the SPARK report

   function Report_File_Is_Empty (Filename : String) return Boolean;
   --  Check if the given file is empty

   procedure Flow_Analysis_And_Proof
     (Project_File : String;
      Proj         : Project_Tree;
      Status       : out Integer);
   --  Translate all source units to Why, using gnat2why, driven by gprbuild.
   --  In the process, do flow analysis. Then call gnatwhy3 inside gnat2why to
   --  prove the program.

   procedure Run_CodePeer
     (Project_File : String;
      Proj         : Project_Tree;
      Status       : out Integer);
   --  Run CodePeer on the project to get the CodePeer results. Do nothing if
   --  CodePeer analysis is disabled.
   --  @param Project_File the project file as a string
   --  @param Proj the project tree object
   --  @param Status out parameter which indicates an error; 0 = OK

   function Spawn_VC_Server
     (Proj_Type : Project_Type)
      return Process_Descriptor;
   --  Spawn the VC server of Why3

   function Text_Of_Step (Step : Gnatprove_Step) return String;

   procedure Set_Environment;
   --  Set the environment before calling other tools.
   --  In particular, add any needed directories in the PATH and
   --  GPR_PROJECT_PATH env vars.

   function Non_Blocking_Spawn
     (Command   : String;
      Arguments : String_Lists.List) return Process_Descriptor;
   --  Spawn a process in a non-blocking way

   procedure Write_Why3_Conf_File (Obj_Dir : String);
   --  Write the Why3 conf file to process prover configuration

   -------------------
   -- Call_Gprbuild --
   -------------------

   procedure Call_Gprbuild
     (Project_File      : String;
      Proj              : Project_Tree;
      DB_Dir            : String;
      Translation_Phase : Boolean;
      Args              : in out String_Lists.List;
      Status            : out Integer)
   is
      Obj_Dir  : constant String :=
         Proj.Root_Project.Artifacts_Dir.Display_Full_Name;
      Opt_File : constant String :=
         Gnat2Why_Opts.Writing.Pass_Extra_Options_To_Gnat2why
            (Translation_Phase => Translation_Phase,
             Obj_Dir           => Obj_Dir,
             Proj_Name         => Project_File);
      Del_Succ : Boolean;

   begin
      Args.Append ("--restricted-to-languages=ada");

      if Minimal_Compile then
         Args.Append ("-m");
      end if;

      Args.Append ("-s");

      for File of CL_Switches.File_List loop
         Args.Append (File);
      end loop;

      if Verbose then
         Args.Append ("-v");
      else
         Args.Append ("-q");
         Args.Append ("-ws");
         Args.Append ("--no-exit-message");
      end if;

      if Parallel > 1 then
         Args.Append ("-j" & Image (Parallel, Min_Width => 1));
      end if;

      if Continue_On_Error then
         Args.Append ("-k");
      end if;

      if Force or else Is_Manual_Prover or else CL_Switches.Replay then
         Args.Append ("-f");
      end if;

      if All_Projects then
         Args.Append ("-U");
      end if;

      Args.Append ("-c");

      for Var of CL_Switches.X loop
         Args.Append (Var);
      end loop;

      if Project_File /= "" then
         Args.Append ("-P");
         Args.Append (Project_File);
      end if;

      Args.Append ("--db");
      Args.Append (DB_Dir);

      if CL_Switches.RTS /= null
        and then CL_Switches.RTS.all /= ""
      then
         Args.Append ("--RTS=" & CL_Switches.RTS.all);
      end if;

      if CL_Switches.Target /= null
        and then CL_Switches.Target.all /= ""
      then
         Args.Append ("--target=" & CL_Switches.Target.all);
      end if;

      for S of CL_Switches.GPR_Project_Path loop
         Args.Append ("-aP");
         Args.Append (S);
      end loop;

      if Debug then
         Args.Append ("-dn");
      end if;

      Args.Append ("-cargs:Ada");
      for Arg of CL_Switches.Cargs_List loop
         Args.Append (Arg);
      end loop;

      Args.Append ("-gnatc");       --  only generate ALI

      Args.Append ("-gnates=" & Opt_File);

      if GnateT_Switch /= null
        and then GnateT_Switch.all /= ""
      then
         Args.Append (Configuration.GnateT_Switch.all);
      end if;

      Call_With_Status
        (Command   => "gprbuild",
         Arguments => Args,
         Status    => Status,
         Verbose   => Verbose);
      if Status = 0 and then not Debug then
         GNAT.OS_Lib.Delete_File (Opt_File, Del_Succ);
      end if;
   end Call_Gprbuild;

   -----------------------------
   -- Compute_ALI_Information --
   -----------------------------

   procedure Compute_ALI_Information
     (Project_File : String;
      Proj         : Project_Tree;
      Status       : out Integer)
   is
      Args : String_Lists.List;
   begin
      declare
         Subd : constant Virtual_File := Phase2_Subdir / Phase1_Subdir;
      begin
         Args.Append ("--subdirs=" & Subd.Display_Full_Name);
      end;
      Args.Append ("--no-object-check");
      Args.Append ("--gnatprove");

      --  Keep going after a compilation error in 'check' mode

      if Configuration.Mode = GPM_Check then
         Args.Append ("-k");
      end if;

      declare
         Cnf_DB : constant String :=
           (if CL_Switches.Coverage then
               SPARK_Install.Gpr_Frames_Cov_DB
            else
               SPARK_Install.Gpr_Frames_DB);
      begin
         Call_Gprbuild (Project_File,
                        Proj,
                        Cnf_DB,
                        Translation_Phase => False,
                        Args              => Args,
                        Status            => Status);
      end;
   end Compute_ALI_Information;

   --------------------
   -- Copy_ALI_Files --
   --------------------

   procedure Copy_ALI_Files (Proj : Project_Tree) is

      procedure Copy_ALI (Source_Dir : Virtual_File);
      --  Copy the ALI files from Source_Dir/Phase1 to Source_Dir

      --------------
      -- Copy_ALI --
      --------------

      procedure Copy_ALI (Source_Dir : Virtual_File) is

         procedure Copy_File (Directory_Entry : Directory_Entry_Type);
         --  copy the file in Argument to Source_Dir

         ---------------
         -- Copy_File --
         ---------------

         procedure Copy_File (Directory_Entry : Directory_Entry_Type) is
            use GNAT.OS_Lib;
            Success : Boolean;
            pragma Unreferenced (Success);
         begin
            Copy_File (Full_Name (Directory_Entry),
                       Source_Dir.Display_Full_Name,
                       Success,
                       Mode => Overwrite,
                       Preserve => Full);
         end Copy_File;

         Phase1_Dir : constant Virtual_File := Source_Dir / Phase1_Subdir;

      --  Start of processing for Copy_ALI

      begin
         if Is_Directory (Phase1_Dir) then
            Search
              (Phase1_Dir.Display_Full_Name,
               Pattern => "*.ali",
               Filter => (Ordinary_File => True, others => False),
               Process => Copy_File'Access);
         end if;
      end Copy_ALI;

      Iter : Project_Iterator := Start (Proj.Root_Project);

   --  Start of processing for Copy_ALI_Files

   begin
      while Current (Iter) /= No_Project loop
         declare
            Art_Dir : Virtual_File renames Current (Iter).Artifacts_Dir;
            Lib_Dir : Virtual_File
            renames Current (Iter).Library_Ali_Directory;
         begin
            if Art_Dir /= No_File then
               Copy_ALI (Art_Dir);
            end if;

            --  In the case of library projects, there is a separate dir where
            --  ALI files are copied at the end. As the first phase was done
            --  with a different subdir, we need to copy those files as well.

            if Lib_Dir /= No_File and then Art_Dir /= Lib_Dir then
               Copy_ALI (Lib_Dir);
            end if;
            Next (Iter);
         end;
      end loop;
   end Copy_ALI_Files;

   ------------------
   -- Execute_Step --
   ------------------

   procedure Execute_Step
     (Plan         : Plan_Type;
      Step         : Positive;
      Project_File : String;
      Proj         : Project_Tree)
   is
      Status : Integer;
   begin
      if not Quiet then
         Put_Line ("Phase" & Positive'Image (Step)
                   & " of" & Positive'Image (Plan'Length)
                   & ": " & Text_Of_Step (Plan (Step)) & " ...");
      end if;

      case Plan (Step) is
         when GS_ALI =>
            Compute_ALI_Information (Project_File, Proj, Status);

         when GS_CodePeer =>
            Run_CodePeer (Project_File, Proj, Status);

         when GS_Gnat2Why =>
            Copy_ALI_Files (Proj);
            Flow_Analysis_And_Proof (Project_File, Proj, Status);

      end case;

      if Status /= 0 then
         Abort_With_Message
           ("gnatprove: error during " & Text_Of_Step (Plan (Step)));
      end if;
   end Execute_Step;

   -----------------------------
   -- Flow_Analysis_And_Proof --
   -----------------------------

   procedure Flow_Analysis_And_Proof
     (Project_File : String;
      Proj         : Project_Tree;
      Status       : out Integer)
   is
      Obj_Dir : constant String :=
        Proj.Root_Project.Artifacts_Dir.Display_Full_Name;

   begin
      Write_Why3_Conf_File (Obj_Dir);

      declare
         use String_Lists;
         Args     : String_Lists.List;
         Del_Succ : Boolean;
         Id       : Process_Descriptor;
      begin
         Args.Append ("--subdirs=" & Phase2_Subdir.Display_Full_Name);

         if IDE_Mode then
            Args.Append ("-d");
         end if;

         if Only_Given or else CL_Switches.No_Subprojects then
            Args.Append ("-u");
         end if;

         --  Replay results if up-to-date. We disable this in debug mode to
         --  be able to see gnat2why output "as it happens", and not only
         --  when gnat2why is finished.

         Args.Append (if Debug
                      then "--no-complete-output"
                      else "--complete-output");

         if Configuration.Mode in GPM_All | GPM_Prove then
            Id := Spawn_VC_Server (Proj.Root_Project);
         end if;

         declare
            Cnf_DB : constant String :=
              (if CL_Switches.Coverage then
                  SPARK_Install.Gpr_Gnat2why_Cov_DB
               else
                  SPARK_Install.Gpr_Translation_DB);
         begin
            Call_Gprbuild (Project_File,
                           Proj,
                           Cnf_DB,
                           Translation_Phase => True,
                           Args              => Args,
                           Status            => Status);
         end;
         if Configuration.Mode in GPM_All | GPM_Prove then
            Close (Id);
            GNAT.OS_Lib.Delete_File (Socket_Name.all, Del_Succ);
            pragma Assert (Del_Succ);
         end if;
      end;
   end Flow_Analysis_And_Proof;

   ---------------------------
   -- Generate_SPARK_Report --
   ---------------------------

   procedure Generate_SPARK_Report
     (Proj     : Project_Type;
      Obj_Dir  : String;
      Obj_Path : File_Array)
   is
      Obj_Dir_Fn : constant String :=
        Ada.Directories.Compose (Obj_Dir, "gnatprove.alfad");
      Success    : Boolean;
      Status     : Integer;
      Args       : String_Lists.List;
      JSON_Rec   : constant JSON_Value := Create_Object;
   begin

      declare
         --  Protect against duplicates in Obj_Path by inserting the items into
         --  a set and only doing something if there item was really inserted.
         --  This is more robust than relying on Obj_Path being sorted.

         Dir_Names_Seen : Configuration.Dir_Name_Sets.Set;

         Inserted       : Boolean;
         Unused         : Dir_Name_Sets.Cursor;

         Obj_Dirs_JSON  : JSON_Array;
      begin
         for Obj of Obj_Path loop
            declare
               Full_Name : String renames Obj.Display_Full_Name;
            begin
               Dir_Names_Seen.Insert (New_Item => Full_Name,
                                      Position => Unused,
                                      Inserted => Inserted);

               if Inserted then
                  Append (Obj_Dirs_JSON, Create (Full_Name));
               end if;
            end;
         end loop;
         Set_Field (JSON_Rec, "obj_dirs", Obj_Dirs_JSON);
      end;

      declare
         use Ada.Command_Line;
         Cmdline_JSON : JSON_Array;
      begin
         Append (Cmdline_JSON, Create (Simple_Name (Command_Name)));
         for J in 1 .. Argument_Count loop
            Append (Cmdline_JSON, Create (Argument (J)));
         end loop;
         Set_Field (JSON_Rec, "cmdline", Cmdline_JSON);
      end;

      if Prj_Attr.Prove.Switches /= null then
         declare
            Switches_JSON : JSON_Array;
         begin
            for Switch of Prj_Attr.Prove.Switches.all loop
               Append (Switches_JSON, Create (Switch.all));
            end loop;
            Set_Field (JSON_Rec, "switches", Switches_JSON);
         end;
      end if;

      if Prj_Attr.Prove.Proof_Switches_Indices'Length > 0 then
         declare
            FS_Switches_JSON : constant JSON_Value := Create_Object;
         begin
            for J of Prj_Attr.Prove.Proof_Switches_Indices.all loop
               declare
                  Switch_Arr : JSON_Array;
               begin
                  for Elt of Prj_Attr.Prove.Proof_Switches (Proj, J.all).all
                  loop
                     Append (Switch_Arr, Create (Elt.all));
                  end loop;
                  Set_Field (FS_Switches_JSON, J.all, Switch_Arr);
               end;
            end loop;
            Set_Field (JSON_Rec, "proof_switches", FS_Switches_JSON);
         end;
      end if;

      declare
         Report_Info_File : File_Type;
         Write_Cont       : constant String := Write (JSON_Rec);
      begin
         Create (Report_Info_File, Out_File, Obj_Dir_Fn);
         Put (Report_Info_File, Write_Cont);
         Close (Report_Info_File);
      end;

      Args.Append (Obj_Dir_Fn);
      if CL_Switches.Assumptions then
         Args.Append ("--assumptions");
         if CL_Switches.Limit_Subp.all /= "" then
            Args.Append ("--limit-subp=" & CL_Switches.Limit_Subp.all);
         end if;
      end if;

      if CL_Switches.Output_Header then
         Args.Append ("--output-header");
      end if;

      Call_With_Status (Command   => "spark_report",
                        Arguments => Args,
                        Status    => Status,
                        Verbose   => Verbose);

      if not Debug then
         GNAT.OS_Lib.Delete_File (Obj_Dir_Fn, Success);
      end if;

      if not Quiet then
         declare
            File : constant String := SPARK_Report_File (Obj_Dir);
         begin
            --  Unless the mode is only checking SPARK legality rules, code in
            --  SPARK will result in either flow or proof results. Otherwise,
            --  the user has probably forgotten to put a SPARK_Mode pragma
            --  somewhere.

            if Configuration.Mode /= GPM_Check then
               if Report_File_Is_Empty (File) then
                  Put_Line
                    (Standard_Error,
                     "warning: no bodies have been analyzed by GNATprove");
                  Put_Line
                    (Standard_Error,
                     "enable analysis of a non-generic body using SPARK_Mode");
               else
                  Put_Line
                    ("Summary logged in " & SPARK_Report_File (Obj_Dir));
               end if;
            end if;
         end;
      end if;

      --  There were unproved checks. If unproved check messages are considered
      --  as errors, issue a failure message and return from gnatprove with a
      --  non-zero error status.

      if CL_Switches.Checks_As_Errors
        and then Status = Unproved_Checks_Error_Status
      then
         Abort_With_Message
           ("gnatprove: unproved check messages considered as errors");

      --  We propagate errors other than the Unproved_Checks_Error

      elsif Status /= 0 and then Status /= Unproved_Checks_Error_Status then
         GNAT.OS_Lib.OS_Exit (Status);
      end if;
   end Generate_SPARK_Report;

   ------------------------
   -- Non_Blocking_Spawn --
   ------------------------

   function Non_Blocking_Spawn
     (Command   : String;
      Arguments : String_Lists.List) return Process_Descriptor
   is
      Executable : String_Access :=
        GNAT.OS_Lib.Locate_Exec_On_Path (Command);
      Args       : GNAT.OS_Lib.Argument_List :=
        Argument_List_Of_String_List (Arguments);
      Proc       : Process_Descriptor;
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
      Non_Blocking_Spawn
        (Proc,
         Executable.all,
         Args,
         Err_To_Out => True);
      Free (Args);
      Free (Executable);
      return Proc;
   end Non_Blocking_Spawn;

   --------------------------
   -- Report_File_Is_Empty --
   --------------------------

   function Report_File_Is_Empty (Filename : String) return Boolean is
   begin
      --  ??? This is a bit of a hack; we assume that the report file is
      --  basically empty when the character count is very low (but not zero).

      return Ada.Directories.Size (Filename) <= 3;
   end Report_File_Is_Empty;

   ------------------
   -- Run_CodePeer --
   ------------------

   procedure Run_CodePeer
     (Project_File : String;
      Proj         : Project_Tree;
      Status       : out Integer)
   is
      pragma Unreferenced (Proj);
      Args : String_Lists.List;

      use type Ada.Containers.Count_Type;
   begin

      if Project_File /= "" then
         Args.Append ("-P");
         Args.Append (Project_File);
      end if;

      if Verbose then
         Args.Append ("-verbose");
      end if;

      if Parallel > 1 then
         Args.Append ("-j" & Image (Parallel, Min_Width => 1));
      end if;

      if All_Projects then
         Args.Append ("-U");
      end if;

      declare
         Steps : constant Integer := File_Specific_Map ("Ada").Steps;
      begin
         if Steps /= 0 then
            Args.Append ("-steps=" & Image (Steps / 10, Min_Width => 1));
         end if;
      end;

      if not Null_Or_Empty_String (CL_Switches.RTS) then
         Args.Append ("--RTS=" & CL_Switches.RTS.all);
      end if;

      if not Null_Or_Empty_String (CL_Switches.Target) then
         Args.Append ("--target=" & CL_Switches.Target.all);
      end if;

      --  ??? we only limit codepeer analysis if the user has given a single
      --  file, and option -u

      if CL_Switches.File_List.Length = 1 and Only_Given then
         Args.Append ("-file");
         for File of CL_Switches.File_List loop
            Args.Append (File);
         end loop;
      end if;

      for Var of CL_Switches.X loop
         Args.Append (Var);
      end loop;

      if not Null_Or_Empty_String (CL_Switches.Subdirs) then
         Args.Append ("--subdirs=" & CL_Switches.Subdirs.all);
      end if;

      if not CL_Switches.GPR_Project_Path.Is_Empty then
         for S of CL_Switches.GPR_Project_Path loop
            Args.Append ("-aP");
            Args.Append (S);
         end loop;
      end if;

      Call_With_Status
        (Command   => "spark_codepeer_wrapper",
         Arguments => Args,
         Status    => Status,
         Verbose   => Verbose);

   end Run_CodePeer;

   ---------------------
   -- Set_Environment --
   ---------------------

   procedure Set_Environment is
      use Ada.Environment_Variables, GNAT.OS_Lib;

      Path_Val : constant String := Value ("PATH", "");
      Gpr_Val  : constant String := Value ("GPR_PROJECT_PATH", "");
      Gpr_Tool : constant String := Value ("GPR_TOOL", "");
      Libgnat  : constant String :=
        Compose (SPARK_Install.Lib, "gnat");
      Sharegpr : constant String :=
        Compose (SPARK_Install.Share, "gpr");
   begin
      --  Unset various environmment variables which might confuse the compiler
      --  or gprbuild.

      Clear ("ADA_INCLUDE_PATH");
      Clear ("ADA_OBJECTS_PATH");
      Clear ("GCC_EXEC_PREFIX");
      Clear ("GCC_ROOT");
      Clear ("GNAT_ROOT");

      --  Add <prefix>/libexec/spark/bin in front of the PATH

      Set ("PATH",
           SPARK_Install.Libexec_Spark_Bin & Path_Separator & Path_Val);

      --  Add <prefix>/lib/gnat & <prefix>/share/gpr in GPR_PROJECT_PATH
      --  so that project files installed with GNAT (not with SPARK)
      --  are found automatically, if any.

      Set ("GPR_PROJECT_PATH",
           Libgnat & Path_Separator & Sharegpr & Path_Separator & Gpr_Val);

      --  Set GPR_TOOL unless already set

      if Gpr_Tool = "" then
         Ada.Environment_Variables.Set ("GPR_TOOL", "gnatprove");
      end if;

   end Set_Environment;

   ---------------------
   -- Spawn_VC_Server --
   ---------------------

   function Spawn_VC_Server
     (Proj_Type : Project_Type)
      return Process_Descriptor
   is
      Args : String_Lists.List;
      Cur  : constant String := Ada.Directories.Current_Directory;
      Id   : Process_Descriptor;
   begin
      Ada.Directories.Set_Directory
        (Proj_Type.Artifacts_Dir.Display_Full_Name);
      Args.Append ("-j");
      Args.Append (Image (Parallel, 1));
      Args.Append ("--socket");
      Args.Append (Socket_Name.all);
      if Debug then
         Args.Append ("--logging");
      end if;
      Id := Non_Blocking_Spawn ("why3server", Args);
      Ada.Directories.Set_Directory (Cur);
      return Id;
   end Spawn_VC_Server;

   ------------------
   -- Text_Of_Step --
   ------------------

   function Text_Of_Step (Step : Gnatprove_Step) return String is
   begin
      --  These strings have to make sense when preceded by
      --  "error during ". See the body of procedure Execute_Step.
      case Step is
         when GS_ALI =>
            if CL_Switches.No_Global_Generation then
               return "generation of program properties";
            else
               return "generation of Global contracts";
            end if;

         when GS_CodePeer =>
            return "CodePeer analysis";

         when GS_Gnat2Why =>
            case Configuration.Mode is
               when GPM_Check =>
                  return "fast partial checking of SPARK legality rules";
               when GPM_Check_All =>
                  return "full checking of SPARK legality rules";
               when GPM_Flow =>
                  return "analysis of data and information flow";
               when GPM_Prove | GPM_All =>
                  return "flow analysis and proof";
            end case;
      end case;
   end Text_Of_Step;

   --------------------------
   -- Write_Why3_Conf_File --
   --------------------------

   procedure Write_Why3_Conf_File (Obj_Dir : String) is

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

      function Build_Prover_Command (Prover    : JSON_Value;
                                     Args_Step : Boolean)
                                     return String;
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
               return "spark_memcached_wrapper " &
                 CL_Switches.Memcached_Server.all & " " &
                 Cmd;
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

      function Build_Prover_Command (Prover    : JSON_Value;
                                     Args_Step : Boolean)
                                     return String
      is
         use Ada.Strings.Unbounded;
         Command  : Unbounded_String;
         Args     : constant JSON_Array := Get (Get (Prover, "args"));
         Args_Add : constant JSON_Array :=
                      (if Args_Step then
                          Get (Get (Prover, "args_steps"))
                       else
                          Get (Get (Prover, "args_time")));
      begin
         Append (Command,
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
         Put_Line (File, Key & " = " & """" & Value & """");
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
         Set_Key_Value ("command",
                        Build_Prover_Command (Editor, Args_Step => False));
      end Write_Editor_Config;

      -------------------------
      -- Write_Prover_Config --
      -------------------------

      procedure Write_Prover_Config (Prover : JSON_Value) is
      begin
         Start_Section ("prover");
         Set_Key_Value ("command",
                        Build_Prover_Command (Prover, Args_Step => False));
         if Has_Field (Prover, "args_steps") then
            Set_Key_Value ("command_steps",
                           Build_Prover_Command (Prover, Args_Step => True));
         end if;
         Set_Key_Value ("driver", Get (Get (Prover, "driver")));
         Set_Key_Value ("name", Get (Get (Prover, "name")));
         Set_Key_Value ("shortcut", Get (Get (Prover, "shortcut")));
         Set_Key_Value ("version", Get (Get (Prover, "version")));
         if Has_Field (Prover, "interactive") then
            Set_Key_Value_Bool ("interactive",
                                Get (Get (Prover, "interactive")));
         end if;
         if Has_Field (Prover, "editor") then
            Set_Key_Value ("editor", Get (Get (Prover, "editor")));
         end if;
         if Has_Field (Prover, "in_place") then
            Set_Key_Value_Bool ("in_place",
                                Get (Get (Prover, "in_place")));
         end if;

      end Write_Prover_Config;

      Config : constant JSON_Value :=
        Read_File_Into_JSON (SPARK_Install.Gnatprove_Conf);

      Editors  : constant JSON_Array := Get (Get (Config, "editors"));
      Provers  : constant JSON_Array := Get (Get (Config, "provers"));
      Filename : constant String := Compose (Obj_Dir, "why3.conf");

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

   Tree : Project_Tree;
   --  GNAT project tree

--  Start processing for Gnatprove

begin
   Set_Environment;
   Read_Command_Line (Tree);

   if Tree.Root_Project.Artifacts_Dir = GNATCOLL.VFS.No_File then
      Abort_With_Message
        ("Error while loading project file: " & CL_Switches.P.all & ": " &
         "could not determine working directory");
   end if;

   declare
      Object_Dir : constant String :=
        Tree.Root_Project.Artifacts_Dir.Display_Full_Name;
   begin
      if not Exists (Object_Dir) then
         Create_Directory (Object_Dir);
      end if;
   end;

   declare
      Plan : constant Plan_Type :=
        (if CodePeer then (GS_ALI, GS_CodePeer, GS_Gnat2Why)
         else (GS_ALI, GS_Gnat2Why));
   begin
      for Step in Plan'Range loop
         Execute_Step (Plan, Step, CL_Switches.P.all, Tree);
      end loop;
   end;

   declare
      Obj_Path : constant File_Array :=
        Object_Path (Tree.Root_Project, Recursive => True);
   begin
      Generate_SPARK_Report
        (Tree.Root_Project,
         Tree.Root_Project.Artifacts_Dir.Display_Full_Name, Obj_Path);
   end;
exception
   when Invalid_Project =>
      Abort_With_Message
         ("Error while loading project file: " & CL_Switches.P.all);
end Gnatprove;
