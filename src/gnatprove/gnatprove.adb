------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                            G N A T P R O V E                             --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2026, AdaCore                     --
--              Copyright (C) 2014-2026, Capgemini Engineering              --
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
with Ada.Directories;
with Ada.Environment_Variables;
with Ada.Exceptions;   use Ada.Exceptions;
with Ada.Strings.Unbounded;
with Ada.Text_IO;      use Ada.Text_IO;
with Call;             use Call;
with Configuration;    use Configuration;
with GNAT.OS_Lib;
with GNAT.Strings;     use GNAT.Strings;
with Gnat2Why_Opts;
with Gnat2Why_Opts.Writing;
with GNATCOLL.JSON;    use GNATCOLL.JSON;
with GNATCOLL.Tribooleans;
with GNATCOLL.Utils;   use GNATCOLL.Utils;
with GNATCOLL.VFS;     use GNATCOLL.VFS;
with GPR2;             use GPR2;
with GPR2.Project.Attribute;
with GPR2.Project.Tree;
with GPR2.Project.View;
with Named_Semaphores; use Named_Semaphores;
with String_Utils;     use String_Utils;
with VC_Kinds;         use VC_Kinds;

procedure Gnatprove with SPARK_Mode is

   type Gnatprove_Step is (GS_Data_Representation, GS_ALI, GS_Gnat2Why);

   type Plan_Type is array (Positive range <>) of Gnatprove_Step;

   Success_Exit_Code : Ada.Command_Line.Exit_Status := 0;
   --  This variable contains the exit code emitted by gnatprove in case of
   --  success. This variable is changed to indicate some error situations that
   --  are not signalled via the GNATprove_Failure exception.

   procedure Call_Gprbuild
     (Project_File      : String;
      Tree              : Project.Tree.Object;
      DB_Dir            : String;
      Translation_Phase : Gnatprove_Step;
      Args              : in out String_Lists.List;
      Status            : out Integer);
   --  Call gprbuild with the given arguments. DB_Dir is the directory
   --  which contains the information to configure gprbuild correctly.

   procedure Create_Dir_And_Parents (Dir : Virtual_File);
   --  Create the directory and necessary parent directories. Do nothing if the
   --  directory already exists. Check if the directory exists. Abort in case
   --  of failure.

   procedure Compute_ALI_Information
     (Project_File : String; Tree : Project.Tree.Object; Status : out Integer);
   --  Compute ALI information for all source units, using gprbuild

   procedure Compute_Data_Representation
     (Project_File : String; Tree : Project.Tree.Object; Status : out Integer);
   --  Compute data representation for all source units, using gprbuild

   procedure Execute_Step
     (Plan         : Plan_Type;
      Step         : Positive;
      Project_File : String;
      Tree         : Project.Tree.Object);

   procedure Copy_ALI_Files (Tree : Project.Tree.Object);
   --  To be called between phase 1 and phase2. Copies the ALI files from the
   --  subdir of the first phase to the one for the second phase.

   procedure Generate_SPARK_Report
     (Tree : Project.Tree.Object; Errors : Boolean);
   --  Generate the SPARK report. Set Errors to True if previous phases
   --  contained errors.

   procedure Flow_Analysis_And_Proof
     (Project_File : String; Tree : Project.Tree.Object; Status : out Integer);
   --  Translate all source units to Why, using gnat2why, driven by gprbuild.
   --  In the process, do flow analysis. Then call gnatwhy3 inside gnat2why to
   --  prove the program.

   function Spawn_VC_Server_And_Semaphore
     (Tree : Project.Tree.Object) return GNAT.OS_Lib.Process_Id;
   --  Spawn the VC server of Why3 and create the semaphore used for gnatwhy3
   --  processes. Also set the environment variables used by the binaries that
   --  access these resources.

   function Text_Of_Step (Step : Gnatprove_Step) return String;

   procedure Set_Environment;
   --  Set the environment before calling other tools.
   --  In particular, add any needed directories in the PATH and
   --  GPR_PROJECT_PATH env vars.

   function Non_Blocking_Spawn
     (Command : String; Arguments : String_Lists.List)
      return GNAT.OS_Lib.Process_Id;
   --  Spawn a process in a non-blocking way

   procedure Write_Why3_Conf_File (Obj_Dir : String);
   --  Write the Why3 conf file to process prover configuration

   procedure Cleanup
     (Tree      : Project.Tree.Object;
      Msg       : String;
      Exit_Code : Ada.Command_Line.Exit_Status);
   --  Cleanup procedure that is called at the end of every gnatprove
   --  execution. Delete temporary files.

   -------------------
   -- Call_Gprbuild --
   -------------------

   procedure Call_Gprbuild
     (Project_File      : String;
      Tree              : Project.Tree.Object;
      DB_Dir            : String;
      Translation_Phase : Gnatprove_Step;
      Args              : in out String_Lists.List;
      Status            : out Integer)
   is
      --  In the first step, gprbuild calls gcc to generate data representation
      --  information. In the second and third steps, it calls gnat2why.
      Call_Gnat2Why : constant Boolean :=
        Translation_Phase /= GS_Data_Representation;
      Obj_Dir       : constant String :=
        Ada.Directories.Full_Name (Artifact_Dir (Tree).Display_Full_Name);
      --  Object directory, without trailing directory separators (e.g. '/')
      Opt_File      : constant String :=
        Gnat2Why_Opts.Writing.Pass_Extra_Options_To_Gnat2why
          (Translation_Phase => Translation_Phase = GS_Gnat2Why,
           Obj_Dir           => Obj_Dir);
      Output_Name   : constant String :=
        (if Call_Gnat2Why
         then ""
         else
           Ada.Directories.Compose
             (Obj_Dir, "data_representation_generation", "log"));
      Del_Succ      : Boolean;

   begin
      Args.Append ("--restricted-to-languages=ada");

      --  We explicitly set the target (which has been already figured out by
      --  the GPR machinery). This way gprbuild will only call gprconfig once:
      --  to generate a configuration for that specific target. Otherwise
      --  gprbuild would make an extra call to gprconfig, just to find the
      --  target.

      Args.Append ("--target=" & String (Tree.Target));

      if Call_Gnat2Why then
         Args.Append ("--gnatprove");  --  Call gnat2why instead of gcc

      end if;

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

      Args.Append ("-j" & Image (Parallel, Min_Width => 1));

      if Continue_On_Error then
         Args.Append ("-k");
      end if;

      if Force or else Has_Manual_Prover or else CL_Switches.Replay then
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

      if Call_Gnat2Why then
         Args.Append ("--db");
         Args.Append (DB_Dir);
      end if;

      if CL_Switches.RTS /= null and then CL_Switches.RTS.all /= "" then
         Args.Append ("--RTS=" & CL_Switches.RTS.all);
      end if;

      if CL_Switches.Target /= null and then CL_Switches.Target.all /= "" then
         Args.Append ("--target=" & CL_Switches.Target.all);
      end if;

      if not Null_Or_Empty_String (CL_Switches.Autoconf) then
         Args.Append ("--autoconf=" & CL_Switches.Autoconf.all);
      end if;

      if not Null_Or_Empty_String (CL_Switches.Config) then
         Args.Append ("--config=" & CL_Switches.Config.all);
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

      if Call_Gnat2Why then
         --  We don't use -gnatc for generating data representation, as it may
         --  lead to incorrect results, and also decreases the precision of the
         --  results.
         Args.Append ("-gnatc");  --  Do not generate an object file
         Args.Append ("-gnates=" & Opt_File);
      else
         Args.Append ("-S");  --  Stop after compilation and do not assemble
         Args.Append ("-gnatR2js");  --  Generate data representation files
         Args.Append ("-gnatws");    --  Suppress all warnings
         Args.Append ("-gnatx");     --  Suppress cross-ref information
      end if;

      if GnateT_Switch /= null and then GnateT_Switch.all /= "" then
         Args.Append (Configuration.GnateT_Switch.all);
      end if;

      if Translation_Phase /= GS_Gnat2Why then
         Args.Append ("-gnatis");  --  Suppress all info messages

      end if;

      Call_With_Status
        (Command     => "gprbuild",
         Arguments   => Args,
         Status      => Status,
         Output_Name => Output_Name,
         Verbose     => Verbose);

      if Status = 0 and then not Debug then
         GNAT.OS_Lib.Delete_File (Opt_File, Del_Succ);
      end if;
   end Call_Gprbuild;

   -------------
   -- Cleanup --
   -------------

   procedure Cleanup
     (Tree      : Project.Tree.Object;
      Msg       : String;
      Exit_Code : Ada.Command_Line.Exit_Status)
   is
      pragma Unreferenced (Tree);
   begin
      if Msg /= "" then
         Ada.Text_IO.Put_Line (Ada.Text_IO.Standard_Error, Msg);
      end if;
      Ada.Command_Line.Set_Exit_Status (Exit_Code);
   end Cleanup;

   -----------------------------
   -- Compute_ALI_Information --
   -----------------------------

   procedure Compute_ALI_Information
     (Project_File : String; Tree : Project.Tree.Object; Status : out Integer)
   is
      Args : String_Lists.List;
   begin
      declare
         Subd : constant Virtual_File := Phase2_Subdir / Phase1_Subdir;
      begin
         Args.Append ("--subdirs=" & Subd.Display_Full_Name);
      end;
      Args.Append ("--no-object-check");

      --  We want to run phase 1 at least on the files that are processed by
      --  phase 2. By not using -u in phase 1 we will obtain a larger set of
      --  files, except when -u was used without files. In addition,
      --  --no-subprojects being equivalent to -u without files, we force -u
      --  when present.

      if (CL_Switches.U and then CL_Switches.File_List.Is_Empty)
        or else (not CL_Switches.U and then CL_Switches.No_Subprojects)
      then
         Args.Append ("-u");
      end if;

      --  Keep going after a compilation error in 'check' mode

      if Configuration.Mode = GPM_Check then
         Args.Append ("-k");
      end if;

      Call_Gprbuild
        (Project_File,
         Tree,
         SPARK_Install.Gpr_Frames_DB,
         Translation_Phase => GS_ALI,
         Args              => Args,
         Status            => Status);
   end Compute_ALI_Information;

   ---------------------------------
   -- Compute_Data_Representation --
   ---------------------------------

   procedure Compute_Data_Representation
     (Project_File : String; Tree : Project.Tree.Object; Status : out Integer)
   is
      Args : String_Lists.List;
   begin
      declare
         Subd : constant Virtual_File :=
           Phase2_Subdir / Data_Representation_Subdir;
      begin
         Args.Append ("--subdirs=" & Subd.Display_Full_Name);
      end;
      Args.Append ("--no-object-check");

      --  Keep going after a compilation error in 'check' mode

      if Configuration.Mode = GPM_Check then
         Args.Append ("-k");
      end if;

      Call_Gprbuild
        (Project_File,
         Tree,
         DB_Dir            => "",
         Translation_Phase => GS_Data_Representation,
         Args              => Args,
         Status            => Status);

      if Status /= 0 then
         if not Quiet then
            Ada.Text_IO.Put_Line
              ("generation of data representation information failed");
            Ada.Text_IO.Put_Line
              ("continuing analysis with partial data representation");
            Ada.Text_IO.Put_Line
              ("for details, see log file "
               & "gnatprove/data_representation_generation.log");
         end if;

         --  Ignore the status of data representation generation, as this is an
         --  optional step in GNATprove.
         Status := 0;
      end if;
   end Compute_Data_Representation;

   --------------------
   -- Copy_ALI_Files --
   --------------------

   procedure Copy_ALI_Files (Tree : Project.Tree.Object) is

      procedure Copy_Dir (Source_Dir, Target_Dir : Virtual_File);
      --  Copy the ALI files from Source_Dir to Target_Dir

      procedure Copy_Phase1 (Target_Dir : Virtual_File);
      --  Copy the ALI files from Target_Dir/Phase1 to Target_Dir

      --------------
      -- Copy_Dir --
      --------------

      procedure Copy_Dir (Source_Dir, Target_Dir : Virtual_File) is

         procedure Copy_File
           (Directory_Entry : Ada.Directories.Directory_Entry_Type);
         --  copy the file in Argument to Target_Dir

         ---------------
         -- Copy_File --
         ---------------

         procedure Copy_File
           (Directory_Entry : Ada.Directories.Directory_Entry_Type)
         is
            use GNAT.OS_Lib;
            Success : Boolean;
            pragma Warnings (Off, Success);  --  modified and then unused

         begin
            Copy_File
              (Ada.Directories.Full_Name (Directory_Entry),
               Target_Dir.Display_Full_Name,
               Success,
               Mode     => Overwrite,
               Preserve => Full);
         end Copy_File;

      begin
         if Is_Directory (Source_Dir) then
            Ada.Directories.Search
              (Source_Dir.Display_Full_Name,
               Pattern => "*.ali",
               Filter  =>
                 [Ada.Directories.Ordinary_File => True, others => False],
               Process => Copy_File'Access);
         end if;
      end Copy_Dir;

      -----------------
      -- Copy_Phase1 --
      -----------------

      procedure Copy_Phase1 (Target_Dir : Virtual_File) is
         Phase1_Dir : constant Virtual_File := Target_Dir / Phase1_Subdir;
      begin
         Copy_Dir (Phase1_Dir, Target_Dir);
      end Copy_Phase1;

      --  Start of processing for Copy_ALI_Files

   begin
      for Cursor in
        Tree.Iterate
          (Status =>
             [GPR2.Project.S_Externally_Built => GNATCOLL.Tribooleans.False])
      loop
         declare
            View : constant Project.View.Object :=
              Project.Tree.Element (Cursor);
         begin
            if View.Kind in With_Object_Dir_Kind then
               Copy_Phase1 (View.Object_Directory.Virtual_File);
            end if;

            --  In the case of library projects, there is a separate dir where
            --  ALI files are copied at the end. As the first phase was done
            --  with a different subdir, we need to copy those files as well.

            if View.Is_Library then
               declare
                  Lib_Dir : Virtual_File renames
                    View.Library_Ali_Directory.Virtual_File;
               begin
                  if View.Kind not in With_Object_Dir_Kind
                    or else View.Object_Directory.Virtual_File /= Lib_Dir
                  then
                     Copy_Dir (View.Object_Directory.Virtual_File, Lib_Dir);
                  end if;
               end;
            end if;
         end;
      end loop;
   end Copy_ALI_Files;

   ----------------------------
   -- Create_Dir_And_Parents --
   ----------------------------

   procedure Create_Dir_And_Parents (Dir : Virtual_File) is
   begin
      if Ada.Directories.Exists (Dir.Display_Full_Name) then
         return;
      end if;
      declare
         Par : constant Virtual_File := Get_Parent (Dir);
      begin
         if Par /= No_File then
            Create_Dir_And_Parents (Par);
         end if;
      end;
      Create_Directory_Or_Exit (Dir.Display_Full_Name);
   end Create_Dir_And_Parents;

   ------------------
   -- Execute_Step --
   ------------------

   procedure Execute_Step
     (Plan         : Plan_Type;
      Step         : Positive;
      Project_File : String;
      Tree         : Project.Tree.Object)
   is
      Status : Integer;
   begin
      if not Quiet then
         Put_Line
           ("Phase"
            & Positive'Image (Step)
            & " of"
            & Positive'Image (Plan'Length)
            & ": "
            & Text_Of_Step (Plan (Step))
            & " ...");
      end if;

      case Plan (Step) is
         when GS_Data_Representation =>
            --  Do not generate data representation if -gnateT is passed
            --  explicity, as the target representation file might not match
            --  the target of the compiler used to generate the data
            --  representation in this phase.
            if Has_gnateT_Switch (Tree.Root_Project)
              or else
                Configuration.Mode in GPM_Check | GPM_Check_All | GPM_Flow
            then
               Status := 0;
            else
               Compute_Data_Representation (Project_File, Tree, Status);
            end if;

         when GS_ALI                 =>
            Compute_ALI_Information (Project_File, Tree, Status);

         when GS_Gnat2Why            =>
            Copy_ALI_Files (Tree);
            Flow_Analysis_And_Proof (Project_File, Tree, Status);
      end case;

      if Status /= 0 then
         declare
            Msg : constant String :=
              "gnatprove: error during " & Text_Of_Step (Plan (Step));
         begin
            if Plan (Step) = GS_Gnat2Why then
               raise GNATprove_Recoverable_Failure with Msg;
            else
               Fail (Msg);
            end if;
         end;
      end if;

   end Execute_Step;

   -----------------------------
   -- Flow_Analysis_And_Proof --
   -----------------------------

   procedure Flow_Analysis_And_Proof
     (Project_File : String; Tree : Project.Tree.Object; Status : out Integer)
   is
      use type GNAT.OS_Lib.Process_Id;
      Obj_Dir : constant String := Artifact_Dir (Tree).Display_Full_Name;
   begin
      Write_Why3_Conf_File (Obj_Dir);

      declare
         use String_Lists;
         Args : String_Lists.List;
         Id   : GNAT.OS_Lib.Process_Id := GNAT.OS_Lib.Invalid_Pid;
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

         Args.Append
           (if Debug then "--no-complete-output" else "--complete-output");

         if Configuration.Mode in GPM_All | GPM_Prove then
            Id := Spawn_VC_Server_And_Semaphore (Tree);
         end if;

         Call_Gprbuild
           (Project_File,
            Tree,
            SPARK_Install.Gpr_Translation_DB,
            Translation_Phase => GS_Gnat2Why,
            Args              => Args,
            Status            => Status);

         if Configuration.Mode in GPM_All | GPM_Prove then
            if Id /= GNAT.OS_Lib.Invalid_Pid then
               GNAT.OS_Lib.Kill (Id, Hard_Kill => False);
               declare
                  Pid    : GNAT.OS_Lib.Process_Id;
                  Unused : Boolean;
               begin
                  --  Wait for the killed process to genlty terminate and for
                  --  the underlying resources to be reclaimed.

                  GNAT.OS_Lib.Wait_Process (Pid, Unused);
                  pragma Assert (Pid = Id);
               end;
            end if;
            if Use_Semaphores then
               Close (Why3_Semaphore);
               Delete (Semaphore_Name);
            end if;
         end if;
      end;
   end Flow_Analysis_And_Proof;

   ---------------------------
   -- Generate_SPARK_Report --
   ---------------------------

   procedure Generate_SPARK_Report
     (Tree : Project.Tree.Object; Errors : Boolean)
   is
      Obj_Dir    : constant String := Artifact_Dir (Tree).Display_Full_Name;
      Obj_Dir_Fn : constant String :=
        Ada.Directories.Compose (Obj_Dir, "gnatprove.alfad");
      Success    : Boolean;
      Status     : Integer;
      Args       : String_Lists.List;
      JSON_Rec   : constant JSON_Value := Create_Object;
      use type Gnat2Why_Opts.Output_Mode_Type;
   begin

      declare
         --  Protect against duplicates in Obj_Path by inserting the items into
         --  a set and only doing something if there item was really inserted.
         --  This is more robust than relying on Obj_Path being sorted.

         Dir_Names_Seen : Configuration.Dir_Name_Sets.Set;

         Inserted : Boolean;
         Unused   : Dir_Name_Sets.Cursor;

         Obj_Dirs_JSON : JSON_Array;
      begin
         for Cursor in
           Tree.Iterate
             (Status =>
                [GPR2.Project.S_Externally_Built =>
                   GNATCOLL.Tribooleans.False])
         loop
            declare
               View : constant Project.View.Object :=
                 Project.Tree.Element (Cursor);
            begin
               if View.Kind in With_Object_Dir_Kind then
                  declare
                     Obj_Dir : constant String :=
                       View.Object_Directory.Virtual_File.Display_Full_Name;
                  begin
                     Dir_Names_Seen.Insert
                       (New_Item => Obj_Dir,
                        Position => Unused,
                        Inserted => Inserted);
                     if Inserted then
                        Append (Obj_Dirs_JSON, Create (Obj_Dir));
                     end if;
                  end;
               end if;
            end;
         end loop;
         Set_Field (JSON_Rec, "obj_dirs", Obj_Dirs_JSON);
      end;

      declare
         use Ada.Command_Line;
         Cmdline_JSON : JSON_Array;
      begin
         Append
           (Cmdline_JSON, Create (Ada.Directories.Simple_Name (Command_Name)));
         for J in 1 .. Argument_Count loop
            Append (Cmdline_JSON, Create (Argument (J)));
         end loop;
         Set_Field (JSON_Rec, "cmdline", Cmdline_JSON);
      end;

      declare
         Attr : constant GPR2.Project.Attribute.Object :=
           Tree.Root_Project.Attribute ((+"Prove", +"Switches"));
      begin
         if Attr.Is_Defined then
            declare
               Switches_JSON : JSON_Array;
            begin
               for Switch of Attr.Values loop
                  Append (Switches_JSON, Create (String (Switch.Text)));
               end loop;
               Set_Field (JSON_Rec, "switches", Switches_JSON);
            end;
         end if;
      end;

      declare
         FS_Switches_JSON : constant JSON_Value := Create_Object;
      begin
         for Attr of
           Tree.Root_Project.Attributes ((+"Prove", +"Proof_Switches"))
         loop
            declare
               Switch_Arr : JSON_Array;
            begin
               for Elt of Attr.Values loop
                  Append (Switch_Arr, Create (String (Elt.Text)));
               end loop;
               Set_Field
                 (FS_Switches_JSON, String (Attr.Index.Text), Switch_Arr);
            end;
         end loop;
         Set_Field (JSON_Rec, "proof_switches", FS_Switches_JSON);
      end;

      if not Null_Or_Empty_String (CL_Switches.Limit_Name)
        or else not Null_Or_Empty_String (CL_Switches.Limit_Subp)
        or else not Null_Or_Empty_String (CL_Switches.Limit_Line)
        or else not Null_Or_Empty_String (CL_Switches.Limit_Lines)
        or else not Null_Or_Empty_String (CL_Switches.Limit_Region)
      then
         Set_Field (JSON_Rec, "has_limit_switches", True);
      end if;

      if CL_Switches.Assumptions then
         Set_Field (JSON_Rec, "assumptions", True);
      end if;

      if Quiet then
         Set_Field (JSON_Rec, "quiet", True);
      end if;

      if CL_Switches.Output_Header then
         Set_Field (JSON_Rec, "output_header", True);
      end if;

      Set_Field (JSON_Rec, "mode", To_JSON (Configuration.Mode));
      Set_Field (JSON_Rec, "has_errors", Errors);

      Set_Field (JSON_Rec, "colors", Output = Gnat2Why_Opts.GPO_Pretty_Color);

      declare
         Report_Info_File : File_Type;
         Write_Cont       : constant String := Write (JSON_Rec);
      begin
         Create (Report_Info_File, Out_File, Obj_Dir_Fn);
         Put (Report_Info_File, Write_Cont);
         Close (Report_Info_File);
      end;

      Args.Append (Obj_Dir_Fn);

      Call_With_Status
        (Command   => "spark_report",
         Arguments => Args,
         Status    => Status,
         Verbose   => Verbose);

      if not Debug then
         GNAT.OS_Lib.Delete_File (Obj_Dir_Fn, Success);
      end if;

      if not Quiet and then Configuration.Mode /= GPM_Check then
         Put_Line ("Summary logged in " & SPARK_Report_File (Obj_Dir));
      end if;

      --  There were unproved checks. If unproved check messages are considered
      --  as errors, issue a failure message and return from gnatprove with a
      --  non-zero error status.

      if Checks_As_Errors and then Status = Unproved_Checks_Error_Status then
         Fail ("gnatprove: unproved check messages considered as errors");

      --  We propagate errors other than the Unproved_Checks_Error

      elsif Status /= 0 and then Status /= Unproved_Checks_Error_Status then
         Success_Exit_Code := Ada.Command_Line.Exit_Status (Status);
      end if;
   end Generate_SPARK_Report;

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
   -- Set_Environment --
   ---------------------

   procedure Set_Environment is
      use Ada.Environment_Variables, GNAT.OS_Lib;

      Path_Val : constant String := Value ("PATH", "");
      Gpr_Val  : constant String := Value ("GPR_PROJECT_PATH", "");
      Gpr_Tool : constant String := Value ("GPR_TOOL", "");
      Libgnat  : constant String :=
        Ada.Directories.Compose (SPARK_Install.Lib, "gnat");
      Sharegpr : constant String :=
        Ada.Directories.Compose (SPARK_Install.Share, "gpr");
   begin
      --  Unset various environmment variables which might confuse the
      --  compiler, gprbuild or why3.

      Clear ("ADA_INCLUDE_PATH");
      Clear ("ADA_OBJECTS_PATH");
      Clear ("GCC_EXEC_PREFIX");
      Clear ("GCC_ROOT");
      Clear ("GNAT_ROOT");
      Clear ("WHY3LIB");
      Clear ("WHY3DATA");
      Clear ("WHY3LOADPATH");
      Clear ("WHY3CONFIG");
      Clear ("WHY3DEBUG");

      --  Add <prefix>/libexec/spark/bin in front of the PATH to find gnatwhy3
      --  and provers. Also add GNSA dir in front of PATH for gprbuild and
      --  other compiler tools.

      Set
        ("PATH",
         SPARK_Install.GNSA_Dir_Bin
         & Path_Separator
         & SPARK_Install.Libexec_Spark_Bin
         & Path_Separator
         & Path_Val);

      --  Add <prefix>/lib/gnat & <prefix>/share/gpr in GPR_PROJECT_PATH so
      --  that project files installed with GNAT (not with SPARK) are found
      --  automatically, if any. But note that the value of GPR_PROJECT_PATH
      --  set by the user should take precedence here, in case of homonyms.

      Set
        ("GPR_PROJECT_PATH",
         Gpr_Val & Path_Separator & Libgnat & Path_Separator & Sharegpr);

      --  Set GPR_TOOL unless already set

      if Gpr_Tool = "" then
         Ada.Environment_Variables.Set ("GPR_TOOL", "gnatprove");
      end if;

   end Set_Environment;

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
         Ada.Directories.Set_Directory (Artifact_Dir (Tree).Display_Full_Name);
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
         declare
            Num_Provers : constant Integer :=
              Integer'Max
                (1, Integer (File_Specific_Map ("default").Provers.Length));
            Max_Proc    : constant Integer :=
              Integer'Max (1, Parallel / Num_Provers);
         begin
            Delete (Semaphore_Name);
            Create (Semaphore_Name, Max_Proc, Why3_Semaphore);
            Ada.Environment_Variables.Set
              ("GNATPROVE_SEMAPHORE", Semaphore_Name);
         end;
      end if;
      return Id;
   end Spawn_VC_Server_And_Semaphore;

   ------------------
   -- Text_Of_Step --
   ------------------

   function Text_Of_Step (Step : Gnatprove_Step) return String is
   begin
      --  These strings have to make sense when preceded by
      --  "error during ". See the body of procedure Execute_Step.
      case Step is
         when GS_Data_Representation =>
            return "generation of data representation information";

         when GS_ALI                 =>
            if CL_Switches.No_Global_Generation then
               return "generation of program properties";
            else
               return "generation of Global contracts";
            end if;

         when GS_Gnat2Why            =>
            case Configuration.Mode is
               when GPM_Check           =>
                  return "fast partial checking of SPARK legality rules";

               when GPM_Check_All       =>
                  return "full checking of SPARK legality rules";

               when GPM_Flow            =>
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
         use Ada.Strings.Unbounded;
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

   Tree : Project.Tree.Object;
   --  GNAT project tree

   --  Start processing for Gnatprove

begin
   Set_Environment;
   Read_Command_Line (Tree);

   if Artifact_Dir (Tree) = GNATCOLL.VFS.No_File then
      Fail
        ("Error while loading project file: "
         & CL_Switches.P.all
         & ": "
         & "could not determine working directory");
   end if;
   Create_Dir_And_Parents (Artifact_Dir (Tree));

   for Cursor in
     Tree.Iterate
       (Kind   =>
          [Project.I_Project       => True,
           Project.I_Runtime       => False,
           Project.I_Configuration => False,
           Project.I_Recursive     => True,
           others                  => False],
        Status =>
          [GPR2.Project.S_Externally_Built => GNATCOLL.Tribooleans.False])
   loop
      declare
         View : constant Project.View.Object := Project.Tree.Element (Cursor);
      begin
         if View.Kind in With_Object_Dir_Kind then
            Create_Dir_And_Parents (View.Object_Directory.Virtual_File);
         end if;
      end;
   end loop;

   Analysis : declare
      Plan : constant Plan_Type :=
        [GS_Data_Representation, GS_ALI, GS_Gnat2Why];
   begin
      for Step in Plan'Range loop
         Execute_Step (Plan, Step, CL_Switches.P.all, Tree);
      end loop;

   exception
      when E : GNATprove_Recoverable_Failure =>
         Generate_SPARK_Report (Tree, Errors => True);
         Fail (Ada.Exceptions.Exception_Message (E));
   end Analysis;

   Generate_SPARK_Report (Tree, Errors => False);
   Cleanup (Tree, "", Success_Exit_Code);

exception
   when E : GNATprove_Failure =>
      Cleanup (Tree, Exception_Message (E), Exit_Code => 1);
   when E : GNATprove_Success =>
      pragma Assert (Exception_Message (E) = "");
      Cleanup (Tree, "", Exit_Code => Success_Exit_Code);
end Gnatprove;
