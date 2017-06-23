------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                            G N A T P R O V E                             --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2017, AdaCore                   --
--                       Copyright (C) 2014-2017, Altran UK Limited         --
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
--      compilation options. Note that this switch is only relevant in phase 2,
--      because in phase 1 these options are mostly irrelevant (and also
--      option -s would not work because we also pass --no-object-check).
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
with Gnat2Why_Args;
with GNATCOLL.JSON;              use GNATCOLL.JSON;
with GNATCOLL.Projects;          use GNATCOLL.Projects;
with GNATCOLL.VFS;               use GNATCOLL.VFS;
with GNATCOLL.Utils;             use GNATCOLL.Utils;
with String_Utils;               use String_Utils;

procedure Gnatprove with SPARK_Mode is

   type Gnatprove_Step is (GS_ALI, GS_CodePeer, GS_Gnat2Why);

   type Plan_Type is array (Positive range <>) of Gnatprove_Step;

   procedure Call_Gprbuild
     (Project_File : String;
      Config_File  : String;
      New_File     : String;
      Args         : in out String_Lists.List;
      Status       : out Integer);
   --  Call gprbuild with the given arguments. Pass in explicitly a number of
   --  parallel processes, so that we can force sequential execution when
   --  needed.

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

   procedure Generate_SPARK_Report
     (Obj_Dir  : String;
      Obj_Path : File_Array);
   --  Generate the SPARK report

   function Report_File_Is_Empty (Filename : String) return Boolean;
   --  Check if the given file is empty

   function Compute_Why3_Args return String_Lists.List;
   --  Compute the list of arguments of gnatwhy3. This list is passed first to
   --  gnat2why, which then passes it to gnatwhy3.

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

   function Pass_Extra_Options_To_Gnat2why
      (Translation_Phase : Boolean;
       Obj_Dir           : String;
       Proj_Name         : String) return String;
   --  Set the environment variable which passes some options to gnat2why.
   --  Translation_Phase is False for globals generation, and True for
   --  translation to Why.

   function Non_Blocking_Spawn
     (Command   : String;
      Arguments : String_Lists.List) return Process_Descriptor;
   --  Spawn a process in a non-blocking way

   function Replace_Config_File_If_Needed
     (Config_File : String;
      New_File    : String) return String;
   --  If option --RTS was not used, do nothing (i.e. return the first
   --  argument). Otherwise, copy the provided config file to a new file with
   --  the name of the second argument while adding the runtime information to
   --  it. Return the second argument.

   procedure Write_Why3_Conf_File (Obj_Dir : String);
   --  Write the Why3 conf file to process prover configuration

   -------------------
   -- Call_Gprbuild --
   -------------------

   procedure Call_Gprbuild
      (Project_File : String;
       Config_File  : String;
       New_File     : String;
       Args         : in out String_Lists.List;
       Status       : out Integer)
   is
      Actual_Config_File : constant String :=
        Replace_Config_File_If_Needed (Config_File, New_File);
   begin

      if Verbose then
         Args.Prepend ("-v");
      else
         Args.Prepend ("-q");
         Args.Prepend ("-ws");
         Args.Prepend ("--no-exit-message");
      end if;

      if Parallel > 1 then
         Args.Prepend ("-j" & Image (Parallel, Min_Width => 1));
      end if;

      if Continue_On_Error then
         Args.Prepend ("-k");
      end if;

      if Force or else Is_Manual_Prover or else CL_Switches.Replay then
         Args.Prepend ("-f");
      end if;

      if No_Inlining then
         Args.Prepend ("-gnatdm");
      end if;

      if All_Projects then
         Args.Prepend ("-U");
      end if;

      Args.Prepend ("-c");

      for Var of CL_Switches.X loop
         Args.Prepend (Var);
      end loop;

      if Project_File /= "" then
         Args.Prepend (Project_File);
         Args.Prepend ("-P");
      end if;

      if Config_File /= "" then
         Args.Prepend ("--config=" & Actual_Config_File);
      end if;

      for S of CL_Switches.GPR_Project_Path loop
         Args.Prepend (S);
         Args.Prepend ("-aP");
      end loop;

      if Debug then
         Args.Prepend ("-dn");
      end if;

      Call_With_Status
        (Command   => "gprbuild",
         Arguments => Args,
         Status    => Status,
         Verbose   => Verbose);
   end Call_Gprbuild;

   -----------------------------
   -- Compute_ALI_Information --
   -----------------------------

   procedure Compute_ALI_Information
     (Project_File : String;
      Proj         : Project_Tree;
      Status       : out Integer)
   is
      Args     : String_Lists.List;
      Obj_Dir  : constant String :=
         Proj.Root_Project.Artifacts_Dir.Display_Full_Name;
      Opt_File : constant String :=
         Pass_Extra_Options_To_Gnat2why
            (Translation_Phase => False,
             Obj_Dir           => Obj_Dir,
             Proj_Name         => Project_File);
      Del_Succ : Boolean;
   begin
      Args.Append ("--subdirs=" & String (Subdir_Name));
      Args.Append ("--restricted-to-languages=ada");
      Args.Append ("--no-object-check");

      for Arg of CL_Switches.Cargs_List loop
         Args.Append (Arg);
      end loop;

      --  Keep going after a compilation error in 'check' mode

      if Configuration.Mode = GPM_Check then
         Args.Append ("-k");
      end if;

      if Minimal_Compile then
         Args.Append ("-m");
      end if;

      for File of CL_Switches.File_List loop
         Args.Append (File);
      end loop;

      Args.Append ("-cargs:Ada");
      Args.Append ("-gnatc");       --  only generate ALI

      Args.Append ("-gnates=" & Opt_File);

      if RTS_Dir.all /= "" then
         Args.Append ("--RTS=" & RTS_Dir.all);
      end if;

      declare
         Cnf_File : constant String :=
           (if CL_Switches.Coverage then
               File_System.Install.Gpr_Frames_Cov_Cnf_File
            else
               File_System.Install.Gpr_Frames_Cnf_File);
      begin
         Call_Gprbuild (Project_File,
                        Cnf_File,
                        Compose (Obj_Dir, File_System.Install.Frames_Cgpr),
                        Args,
                        Status);
      end;
      if Status = 0 and then not Debug then
         GNAT.OS_Lib.Delete_File (Opt_File, Del_Succ);
      end if;
   end Compute_ALI_Information;

   -----------------------
   -- Compute_Why3_Args --
   -----------------------

   function Compute_Why3_Args return String_Lists.List is

      Args    : String_Lists.List;
      Why3_VF : constant Virtual_File :=
        (if Why3_Config_File.all /= ""
         then Create (Filesystem_String (Why3_Config_File.all))
         else No_File);
      Gnatwhy3_Conf : constant String :=
        (if Why3_VF /= No_File then
           (if Is_Absolute_Path (Why3_VF)
            then Why3_Config_File.all
            else Compose (+Get_Current_Dir.Full_Name, Why3_Config_File.all))
         else "");

      -------------------------
      --  Local subprograms  --
      -------------------------

      procedure Prepare_Why3_Manual;
      --  Build user libraries (if any) for manual provers

      ---------------------------
      --  Prepare_Why3_Manual  --
      ---------------------------

      procedure Prepare_Why3_Manual is
         Args : GNAT.OS_Lib.Argument_List :=
           (if Gnatwhy3_Conf /= "" then
              (1 => new String'("--prepare-shared"),
               2 => new String'("--prover"),
               3 => new String'(Prover_List),
               4 => new String'("--proof-dir"),
               5 => new String'(Proof_Dir.all),
               6 => new String'("--why3-conf"),
               7 => new String'(Gnatwhy3_Conf))
            else
              (1 => new String'("--prepare-shared"),
               2 => new String'("--prover"),
               3 => new String'(Prover_List),
               4 => new String'("--proof-dir"),
               5 => new String'(Proof_Dir.all)));
         Res : Boolean;
         Old_Dir  : constant String := Current_Directory;
         Gnatwhy3 : constant String :=
           Compose (File_System.Install.Libexec_Spark_Bin, "gnatwhy3");
      begin
         Set_Directory  (Main_Subdir.all);
         if Verbose then
            Ada.Text_IO.Put (Gnatwhy3 & " ");
            for Arg of Args loop
               Ada.Text_IO.Put (Arg.all & " ");
            end loop;
            Ada.Text_IO.New_Line;
         end if;
         GNAT.OS_Lib.Spawn (Program_Name => Gnatwhy3,
                            Args => Args,
                            Success => Res);
         for It in Args'Range loop
            Free (Args (It));
         end loop;
         Set_Directory (Old_Dir);
         if not Res then
            Ada.Text_IO.Put_Line (Ada.Text_IO.Standard_Error,
                                  "Failed to compile shared");
            GNAT.OS_Lib.OS_Exit (1);
         end if;
      end Prepare_Why3_Manual;

   --  Start of processing for Compute_Why3_Args

   begin

      --  the first "argument" is in fact the command name itself, because in
      --  some cases we might want to change it

      if Memcached_Server /= null and then Memcached_Server.all /= "" then
         Args.Append ("spark_memcached_wrapper");
         Args.Append (Memcached_Server.all);
         Args.Append ("gnatwhy3");
      else
         Args.Append ("gnatwhy3");
      end if;

      --  If not set explicitly, the code above always sets a suitable value
      --  for the prover list, the proof strategy and the steps limit. No
      --  value of timeout may be set though, which is expected in general
      --  for deterministic behavior.

      Args.Append ("--timeout");
      Args.Append (Image (Timeout, 1));

      Args.Append ("--steps");
      Args.Append (Image (Steps, 1));

      if not Provers.Is_Empty then
         Args.Append ("--prover");
         Args.Append (Prover_List);
      end if;

      Args.Append ("--proof");
      Args.Append (To_String (Proof));

      Args.Append ("--socket");
      Args.Append (Socket_Name.all);

      if Debug then
         Args.Append ("--debug");
      end if;

      if Force then
         Args.Append ("--force");
      end if;

      if not Lazy then
         Args.Append ("--prove-all");
      end if;

      if CL_Switches.Replay then
         Args.Append ("--replay");
      end if;

      Args.Append ("-j");
      Args.Append (Image (Parallel, 1));

      if Limit_Line.all /= "" then
         Args.Append ("--limit-line");
         Args.Append (Limit_Line.all);
      end if;
      if Limit_Subp.all /= "" then
         Args.Append ("--limit-subp");
         Args.Append (Limit_Subp.all);
      end if;

      if Proof_Dir /= null then
         pragma Assert (Proof_Dir.all /= "");
         Create_Path (Compose (Proof_Dir.all, "sessions"));
         Args.Append ("--proof-dir");
         --  Why3 is executed in the gnatprove directory and does not know
         --  the project directory so we give it an absolute path to the
         --  proof_dir.
         Args.Append (Proof_Dir.all);
         if Is_Manual_Prover then
            Prepare_Why3_Manual;
         end if;
      end if;

      if Gnatwhy3_Conf /= "" then
         Args.Append ("--why3-conf");
         Args.Append (Gnatwhy3_Conf);
      end if;

      Args.Append ("--counterexample");
      if Counterexample then
         Args.Append ("on");
      else
         Args.Append ("off");
      end if;

      if Z3_Counterexample then
         Args.Append ("--ce_prover");
         Args.Append ("z3_ce");
      end if;

      Args.Append ("--ce-timeout");
      Args.Append (Image (CE_Timeout, 1));

      return Args;
   end Compute_Why3_Args;

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
            Flow_Analysis_And_Proof (Project_File, Proj, Status);

      end case;

      if Status /= 0
        and then (Configuration.Mode = GPM_Check
                  or else Configuration.Mode = GPM_Check_All)
      then
         Status := 0;
      end if;

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
         Opt_File : constant String :=
           Pass_Extra_Options_To_Gnat2why
             (Translation_Phase => True,
              Obj_Dir           => Obj_Dir,
              Proj_Name         => Project_File);
         Del_Succ : Boolean;
         pragma Unreferenced (Del_Succ);
         Id       : Process_Descriptor;
      begin

         Args.Append ("--subdirs=" & String (Subdir_Name));
         Args.Append ("--restricted-to-languages=ada");
         Args.Append ("-s");

         if Minimal_Compile then
            Args.Append ("-m");
         end if;

         if IDE_Mode then
            Args.Append ("-d");
         end if;

         if Only_Given then
            Args.Append ("-u");
         end if;

         for File of CL_Switches.File_List loop
            Args.Append (File);
         end loop;

         Args.Append ("-cargs:Ada");
         Args.Append ("-gnatc");              --  No object file generation

         --  Replay results if up-to-date. We disable this in debug mode to
         --  be able to see gnat2why output "as it happens", and not only
         --  when gnat2why is finished.

         if Debug then
            Args.Prepend ("--no-complete-output");
         else
            Args.Prepend ("--complete-output");
         end if;

         Args.Append ("-gnates=" & Opt_File);

         for Carg of CL_Switches.Cargs_List loop
            Args.Append (Carg);
         end loop;
         if RTS_Dir.all /= "" then
            Args.Append ("--RTS=" & RTS_Dir.all);
         end if;

         Id := Spawn_VC_Server (Proj.Root_Project);

         declare
            Cnf_File : constant String :=
              (if CL_Switches.Coverage then
                  File_System.Install.Gpr_Gnat2why_Cov_Cnf_File
               else
                  File_System.Install.Gpr_Translation_Cnf_File);
         begin
            Call_Gprbuild (Project_File,
                           Cnf_File,
                           Compose (Obj_Dir,
                             File_System.Install.Gnat2why_Cgpr),
                           Args,
                           Status);
         end;
         if Status = 0 and then not Debug then
            GNAT.OS_Lib.Delete_File (Opt_File, Del_Succ);
         end if;
         Close (Id);
         GNAT.OS_Lib.Delete_File
           (Compose (Proj.Root_Project.Artifacts_Dir.Display_Full_Name,
            Socket_Name.all), Del_Succ);
      end;
   end Flow_Analysis_And_Proof;

   ---------------------------
   -- Generate_SPARK_Report --
   ---------------------------

   procedure Generate_SPARK_Report
     (Obj_Dir  : String;
      Obj_Path : File_Array)
   is
      Obj_Dir_File : File_Type;
      Obj_Dir_Fn   : constant String :=
        Ada.Directories.Compose (Obj_Dir, "gnatprove.alfad");

      Success      : Boolean;

      Args         : String_Lists.List;

   begin
      Create (Obj_Dir_File, Out_File, Obj_Dir_Fn);
      declare
         --  Protect against duplicates in Obj_Path by inserting the items into
         --  a set and only doing something if there item was really inserted.
         --  This is more robust than relying on Obj_Path being sorted.

         Dir_Names_Seen : Configuration.Dir_Name_Sets.Set;

         Inserted : Boolean;
         Unused   : Dir_Name_Sets.Cursor;

      begin
         for Index in Obj_Path'Range loop
            declare
               Full_Name : String renames Obj_Path (Index).Display_Full_Name;
            begin
               Dir_Names_Seen.Insert (New_Item => Full_Name,
                                      Position => Unused,
                                      Inserted => Inserted);

               if Inserted then
                  Put_Line (Obj_Dir_File, Full_Name);
               end if;
            end;
         end loop;
      end;
      Close (Obj_Dir_File);

      Args.Append (Obj_Dir_Fn);
      if CL_Switches.Assumptions then
         Args.Append ("--assumptions");
         if Limit_Subp.all /= "" then
            Args.Append ("--limit-subp=" & Limit_Subp.all);
         end if;
      end if;

      if CL_Switches.Output_Header then
         Args.Append ("--output-header");
      end if;

      Call_Exit_On_Failure
        (Command   => "spark_report",
         Arguments => Args,
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

            if Configuration.Mode /= GPM_Check
              and then Report_File_Is_Empty (File)
            then
               Put_Line
                 (Standard_Error,
                  "warning: no bodies have been analyzed by GNATprove");
               Put_Line
                 (Standard_Error,
                  "enable analysis of a body using SPARK_Mode");
            else
               Put_Line ("Summary logged in " & SPARK_Report_File (Obj_Dir));
            end if;
         end;
      end if;
   end Generate_SPARK_Report;

   ------------------------
   -- Non_Blocking_Spawn --
   ------------------------

   function Non_Blocking_Spawn
     (Command   : String;
      Arguments : String_Lists.List) return Process_Descriptor is
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

   ------------------------------------
   -- Pass_Extra_Options_To_Gnat2why --
   ------------------------------------

   function Pass_Extra_Options_To_Gnat2why
      (Translation_Phase : Boolean;
       Obj_Dir           : String;
       Proj_Name         : String) return String is
      use Ada.Strings.Unbounded;
   begin
      --  Always set debug flags

      Gnat2Why_Args.Debug_Mode := Debug;
      Gnat2Why_Args.Flow_Advanced_Debug := Flow_Extra_Debug;
      Gnat2Why_Args.Flow_Generate_Contracts :=
        not Configuration.No_Global_Generation;

      --  In the translation phase, set a number of values

      if Translation_Phase then
         Gnat2Why_Args.Global_Gen_Mode := False;
         Gnat2Why_Args.Warning_Mode := Warning_Mode;
         Gnat2Why_Args.Check_Mode := Configuration.Mode = GPM_Check;
         Gnat2Why_Args.Check_All_Mode := Configuration.Mode = GPM_Check_All;
         Gnat2Why_Args.Flow_Analysis_Mode := Configuration.Mode = GPM_Flow;
         Gnat2Why_Args.Prove_Mode := Configuration.Mode = GPM_Prove;
         Gnat2Why_Args.Flow_Termination_Proof := Flow_Termination;
         Gnat2Why_Args.Flow_Show_GG := Flow_Show_GG;
         Gnat2Why_Args.Proof_Generate_Guards :=
           not Configuration.No_Axiom_Guard;
         Gnat2Why_Args.Ide_Mode := IDE_Mode;
         Gnat2Why_Args.Pedantic := CL_Switches.Pedantic;
         Gnat2Why_Args.Limit_Subp :=
           Ada.Strings.Unbounded.To_Unbounded_String (Limit_Subp.all);
         Gnat2Why_Args.Limit_Line :=
           Ada.Strings.Unbounded.To_Unbounded_String (Limit_Line.all);
         Gnat2Why_Args.Why3_Args := Compute_Why3_Args;
         Gnat2Why_Args.Report_Mode := Report;
         Gnat2Why_Args.Why3_Dir := To_Unbounded_String (Obj_Dir);
         if CodePeer then
            Gnat2Why_Args.CP_Res_Dir :=
              To_Unbounded_String
                (Compose
                   (Compose
                      (Compose (Obj_Dir, "codepeer"),
                       Base_Name (Proj_Name) & ".output"),
                    "sam"));
         end if;

      --  In the globals generation phase, only set Global_Gen_Mode

      else
         Gnat2Why_Args.Global_Gen_Mode := True;
      end if;

      return Gnat2Why_Args.Set (Obj_Dir);
   end Pass_Extra_Options_To_Gnat2why;

   -----------------------------------
   -- Replace_Config_File_If_Needed --
   -----------------------------------

   function Replace_Config_File_If_Needed
     (Config_File : String;
      New_File    : String) return String
   is
      Handle     : File_Type;
      RTS_Set    : Boolean;
      Target_Set : Boolean;

      procedure Copy_Replace_Line (Line : String);
      --  Copy the given line over to Handle. If the line corresponds to the
      --  Runtime_Library_Dir pattern, replace it by
      --    for Runtime_Library_Dir ("Ada") use ("dir");

      -----------------------
      -- Copy_Replace_Line --
      -----------------------

      procedure Copy_Replace_Line (Line : String) is
      begin
         if RTS_Set and then
           GNATCOLL.Utils.Starts_With (Line, "--RUNTIME_LIBRARY_DIR")
         then
            Put_Line
              (Handle,
               " for Runtime_Library_Dir (""Ada"") use """ & RTS_Dir.all &
                 """;");
         elsif Target_Set and then
           GNATCOLL.Utils.Starts_With (Line, "--TARGET")
         then
            Put_Line
              (Handle,
               " for Target use """ & Prj_Attr.Target.all & """;");
         else
            Put_Line (Handle, Line);
         end if;
      end Copy_Replace_Line;

      procedure Copy_File is new For_Line_In_File (Copy_Replace_Line);

   --  Start of processing for Replace_Config_File_If_Needed

   begin
      if RTS_Dir.all = "" and then
        Null_Or_Empty_String (Prj_Attr.Target)
      then
         return Config_File;
      end if;

      RTS_Set    := RTS_Dir.all /= "";
      Target_Set := not Null_Or_Empty_String (Prj_Attr.Target);

      Create (Handle, Out_File, New_File);
      Copy_File (Config_File);
      Close (Handle);
      return New_File;
   end Replace_Config_File_If_Needed;

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

      if RTS_Dir.all /= "" then
         Args.Append ("--RTS=" & RTS_Dir.all);
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
      use Ada.Environment_Variables, GNAT.OS_Lib, Ada.Strings.Unbounded;

      Path_Val : constant String := Value ("PATH", "");
      Gpr_Val  : constant String := Value ("GPR_PROJECT_PATH", "");
      Libgnat  : constant String :=
        Compose (File_System.Install.Lib, "gnat");
      Sharegpr : constant String :=
        Compose (File_System.Install.Share, "gpr");

      Cmd_Line : Unbounded_String :=
        To_Unbounded_String
          (Ada.Directories.Simple_Name (Ada.Command_Line.Command_Name));
      --  The full command line

   begin
      --  Add <prefix>/libexec/spark/bin in front of the PATH

      Set ("PATH",
           File_System.Install.Libexec_Spark_Bin & Path_Separator & Path_Val);

      --  Add <prefix>/lib/gnat & <prefix>/share/gpr in GPR_PROJECT_PATH
      --  so that project files installed with GNAT (not with SPARK)
      --  are found automatically, if any.

      Set ("GPR_PROJECT_PATH",
           Libgnat & Path_Separator & Sharegpr & Path_Separator & Gpr_Val);

      --  Add full command line in environment for printing in header of
      --  generated file "gnatprove.out"

      for J in 1 .. Ada.Command_Line.Argument_Count loop
         Append (Cmd_Line, " ");
         Append (Cmd_Line, Ada.Command_Line.Argument (J));
      end loop;
      Set ("GNATPROVE_CMD_LINE", To_String (Cmd_Line));

   end Set_Environment;

   ---------------------
   -- Spawn_VC_Server --
   ---------------------

   function Spawn_VC_Server
     (Proj_Type : Project_Type)
      return Process_Descriptor is
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
            if Configuration.No_Global_Generation then
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

      Config : constant JSON_Value :=
        Read (Read_File_Into_String (File_System.Install.Gnatprove_Conf));
      File : File_Type;

      procedure Start_Section (Name : String);
      --  start a section in the why3.conf file

      procedure Set_Key_Value (Key, Value : String);
      --  write a line 'key = "value"' to the why3.conf file

      procedure Set_Key_Value_Int (Key : String; Value : Integer);
      --  same, but for Integers. We do not use overloading, because in
      --  connection with the overloading of JSON API, this will require type
      --  annotations.

      procedure Write_Prover_Config (Prover : JSON_Value);
      --  write the config of a prover

      procedure Write_Editor_Config (Editor : JSON_Value);
      --  write the config of an editor

      function Build_Prover_Command (Prover : JSON_Value) return String;
      --  given a prover configuration in JSON, construct the prover command
      --  for why3.conf

      function Build_Steps_Command (Prover : JSON_Value) return String;
      --  same as Build_Prover_Command, but also add the extra arguments for
      --  steps. The last argument of the regular arguments is preserved, that
      --  is, the extra arguments for steps are added just before.

      function Build_Executable (Exec : String) return String;
      --  build the part of a command that corresponds to the executable. Takes
      --  into account Benchmark mode.

      ----------------------
      -- Build_Executable --
      ----------------------

      function Build_Executable (Exec : String) return String is
      begin
         if CL_Switches.Benchmark then
            return "fake_" & Exec;
         end if;
         return Exec;
      end Build_Executable;

      --------------------------
      -- Build_Prover_Command --
      --------------------------

      function Build_Prover_Command (Prover : JSON_Value) return String is
         use Ada.Strings.Unbounded;
         Command : Unbounded_String;
         Args : constant JSON_Array := Get (Get (Prover, "args"));
      begin
         Append (Command,
                 Build_Executable (String'(Get (Get (Prover, "executable")))));
         for Index in 1 .. Length (Args) loop
            Append (Command, " " & String'(Get (Get (Args, Index))));
         end loop;
         return To_String (Command);
      end Build_Prover_Command;

      -------------------------
      -- Build_Steps_Command --
      -------------------------

      function Build_Steps_Command (Prover : JSON_Value) return String is
         use Ada.Strings.Unbounded;
         Command : Unbounded_String;
         Args : constant JSON_Array := Get (Get (Prover, "args"));
         Args_Steps : constant JSON_Array := Get (Get (Prover, "args_steps"));
      begin
         Append (Command,
                 Build_Executable (String'(Get (Get (Prover, "executable")))));
         for Index in 1 .. Length (Args) - 1 loop
            Append (Command, " " & String'(Get (Get (Args, Index))));
         end loop;
         for Index in 1 .. Length (Args_Steps) loop
            Append (Command, " " & String'(Get (Get (Args_Steps, Index))));
         end loop;
         Append (Command, " " & String'(Get (Get (Args, Length (Args)))));
         return To_String (Command);
      end Build_Steps_Command;

      -------------------
      -- Set_Key_Value --
      -------------------

      procedure Set_Key_Value (Key, Value : String) is
      begin
         Put_Line (File, Key & " = " & """" & Value & """");
      end Set_Key_Value;

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
         Set_Key_Value ("command", Build_Prover_Command (Editor));
      end Write_Editor_Config;

      -------------------------
      -- Write_Prover_Config --
      -------------------------

      procedure Write_Prover_Config (Prover : JSON_Value) is
      begin
         Start_Section ("prover");
         Set_Key_Value ("command", Build_Prover_Command (Prover));
         if Has_Field (Prover, "args_steps") then
            Set_Key_Value ("command_steps", Build_Steps_Command (Prover));
         end if;
         Set_Key_Value ("driver", Get (Get (Prover, "driver")));
         Set_Key_Value ("name", Get (Get (Prover, "name")));
         Set_Key_Value ("shortcut", Get (Get (Prover, "shortcut")));
         Set_Key_Value ("version", Get (Get (Prover, "version")));
      end Write_Prover_Config;

      Editors : constant JSON_Array := Get (Get (Config, "editors"));
      Provers : constant JSON_Array := Get (Get (Config, "provers"));
      Filename : constant String := Compose (Obj_Dir, "why3.conf");

      --  Start of Processing of Write_Why3_Conf_File

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

   Tree      : Project_Tree;
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
        (Tree.Root_Project.Artifacts_Dir.Display_Full_Name, Obj_Path);
   end;
exception
   when Invalid_Project =>
      Abort_With_Message
         ("Error while loading project file: " & CL_Switches.P.all);
end Gnatprove;
