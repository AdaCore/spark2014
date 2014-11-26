------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                            G N A T P R O V E                             --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2014, AdaCore                   --
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

with Ada.Directories;    use Ada.Directories;
with Ada.Environment_Variables;
with Ada.Strings.Unbounded;
with Ada.Text_IO;        use Ada.Text_IO;
with Call;               use Call;
with Configuration;      use Configuration;

with GNAT.Expect;        use GNAT.Expect;
with GNAT.OS_Lib;

with GNATCOLL.Projects;  use GNATCOLL.Projects;
with GNATCOLL.VFS;       use GNATCOLL.VFS;
with GNATCOLL.Utils;     use GNATCOLL.Utils;

with GNAT.Strings;       use GNAT.Strings;
with String_Utils;       use String_Utils;

with Gnat2Why_Args;

procedure Gnatprove is

   type Gnatprove_Step is (GS_ALI, GS_Gnat2Why);

   function Step_Image (S : Gnatprove_Step) return String is
      (Int_Image (Gnatprove_Step'Pos (S) + 1));

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
       Status : out Integer);
   --  Compute ALI information for all source units, using gprbuild.

   procedure Execute_Step
      (Step         : Gnatprove_Step;
       Project_File : String;
       Proj         : Project_Tree);

   procedure Generate_SPARK_Report
     (Obj_Dir : String;
      Obj_Path  : File_Array);
   --  Generate the SPARK report.

   function Report_File_Is_Empty (Filename : String) return Boolean;
   --  Check if the given file is empty

   procedure Generate_Why3_Conf_File
     (Gnatprove_Subdir : String);

   function Compute_Why3_Args return String_Lists.List;
   --  compute the list of arguments of gnatwhy3. This list is passed first to
   --  gnat2why, which then passes it to gnatwhy3

   procedure Flow_Analysis_And_Proof
      (Project_File     : String;
       Proj             : Project_Tree;
       Status           : out Integer);
   --  Translate all source units to Why, using gnat2why, driven by gprbuild.
   --  In the process, do flow analysis. Then call gnatwhy3 inside gnat2why to
   --  prove the program.

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
       Obj_Dir           : String) return String;
   --  Set the environment variable which passes some options to gnat2why.
   --  Translation_Phase is False for globals generation, and True for
   --  translation to Why.

   function Non_Blocking_Spawn
     (Command   : String;
      Arguments : String_Lists.List) return Process_Descriptor;
   --  spawn a process in a non-blocking way

   procedure Kill (P : in out Process_Descriptor);
   --  kill the process

   function Replace_Config_File_If_Needed
     (Config_File : String;
      New_File    : String) return String;
   --  if option --RTS was not used, do nothing (i.e. return the first
   --  argument). Otherwise, copy the provided config file to a new file with
   --  the name of the second argument while adding the runtime information to
   --  it. Return the second argument.

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
         Args.Prepend ("-j" & Int_Image (Parallel));
      end if;

      if Continue_On_Error then
         Args.Prepend ("-k");
      end if;

      if Force then
         Args.Prepend ("-f");
      end if;

      if All_Projects then
         Args.Prepend ("-U");
      end if;

      Args.Prepend ("-c");

      for Var of Configuration.Scenario_Variables loop
         Args.Prepend (Var);
      end loop;

      if Project_File /= "" then
         Args.Prepend (Project_File);
         Args.Prepend ("-P");
      end if;

      if Config_File /= "" then
         Args.Prepend ("--config=" & Actual_Config_File);
      end if;

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
      use String_Lists;
      Args     : List := Empty_List;
      Obj_Dir  : constant String :=
         Proj.Root_Project.Object_Dir.Display_Full_Name;
      Opt_File : constant String :=
         Pass_Extra_Options_To_Gnat2why
            (Translation_Phase => False,
             Obj_Dir           => Obj_Dir);
      Del_Succ : Boolean;
   begin
      Args.Append ("--subdirs=" & String (Subdir_Name));
      Args.Append ("--restricted-to-languages=ada");
      Args.Append ("--no-object-check");

      for Arg of Cargs_List loop
         Args.Append (Arg);
      end loop;

      --  Keep going after a compilation error in 'check' mode

      if MMode = GPM_Check then
         Args.Append ("-k");
      end if;

      if Minimal_Compile then
         Args.Append ("-m");
      end if;

      for File of File_List loop
         Args.Append (File);
      end loop;

      Args.Append ("-cargs:Ada");
      Args.Append ("-gnatc");       --  only generate ALI

      Args.Append ("-gnates=" & Opt_File);

      if RTS_Dir.all /= "" then
         Args.Append ("--RTS=" & RTS_Dir.all);
      end if;

      Call_Gprbuild (Project_File,
                     Gpr_Frames_Cnf_File,
                     Compose (Obj_Dir, Frames_Cgpr),
                     Args,
                     Status);
      if Status = 0 and then not Debug then
         GNAT.OS_Lib.Delete_File (Opt_File, Del_Succ);
      end if;
   end Compute_ALI_Information;

   -----------------------
   -- Compute_Why3_Args --
   -----------------------

   function Compute_Why3_Args return String_Lists.List is
      Args : String_Lists.List := String_Lists.Empty_List;
      Gnatwhy3_Conf : constant String :=
        (if Why3_Config_File /= null
         and then Why3_Config_File.all /= ""
         then
            Compose (+Get_Current_Dir.Full_Name, Why3_Config_File.all)
         else "");
      ---------------------------
      --  Prepare_Why3_Manual  --
      ---------------------------

      procedure Prepare_Why3_Manual;

      procedure Prepare_Why3_Manual is
         Args : GNAT.OS_Lib.Argument_List :=
           (if Gnatwhy3_Conf /= "" then
              (1 => new String'("--prepare-shared"),
               2 => new String'("--prover"),
               3 => new String'(Alter_Prover.all),
               4 => new String'("--proof-dir"),
               5 => new String'(Proof_Dir.all),
               6 => new String'("--why3-conf"),
               7 => new String'(Gnatwhy3_Conf))
            else
              (1 => new String'("--prepare-shared"),
               2 => new String'("--prover"),
               3 => new String'(Alter_Prover.all),
               4 => new String'("--proof-dir"),
               5 => new String'(Proof_Dir.all)));
         Res : Boolean;
         Old_Dir : constant String := Current_Directory;
         Gnatwhy3 : constant String := Compose (Compose (Prefix, "bin"),
                                                "gnatwhy3");
      begin
         Set_Directory  (Main_Subdir.all);
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

   begin
      if Timeout /= 0 then
         Args.Append ("--timeout");
         Args.Append (Int_Image (Timeout));
      end if;

      --  The steps option is passed to alt-ergo via the why3.conf file. We
      --  still need to pass it to gnatwhy3 as well so that it is aware of the
      --  value of that switch.

      if Steps /= 0 then
         Args.Append ("--steps");
         Args.Append (Int_Image (Steps));
      end if;
      Args.Append ("--socket");
      Args.Append (Socket_Name.all);
      if Debug then
         Args.Append ("--debug");
      end if;
      if Force then
         Args.Append ("--force");
      end if;
      if Proof /= Then_Split then
         Args.Append ("--proof");
         Args.Append (To_String (Proof));
      end if;

      if not Lazy then
         Args.Append ("--prove-all");
      end if;

      Args.Append ("-j");
      Args.Append (Int_Image (Parallel));

      if Limit_Line /= null and then Limit_Line.all /= "" then
         Args.Append ("--limit-line");
         Args.Append (Limit_Line.all);
      end if;
      if Limit_Subp /= null and then Limit_Subp.all /= "" then
         Args.Append ("--limit-subp");
         Args.Append (Limit_Subp.all);
      end if;
      if Alter_Prover /= null and then Alter_Prover.all /= "" then
         Args.Append ("--prover");
         Args.Append (Alter_Prover.all);
      end if;

      if Proof_Dir /= null then
         pragma Assert (Proof_Dir.all /= "");
         Create_Path (Compose (Proof_Dir.all, "sessions"));
         Args.Append ("--proof-dir");
         --  Why3 is executed in the gnatprove directory and does not know
         --  the project directory so we give it an absolute path to the
         --  proof_dir
         Args.Append (Proof_Dir.all);
         if Alter_Prover /= null and then Alter_Prover.all /= "" then
            Prepare_Why3_Manual;
         end if;
      end if;

      if Gnatwhy3_Conf /= "" then
         Args.Append ("--why3-conf");
         Args.Append (Gnatwhy3_Conf);
      end if;

      return Args;
   end Compute_Why3_Args;

   ------------------
   -- Execute_Step --
   ------------------

   procedure Execute_Step
     (Step         : Gnatprove_Step;
      Project_File : String;
      Proj         : Project_Tree)
   is
      Status : Integer;
   begin
      if not Quiet then
         Put_Line ("Phase " & Step_Image (Step)
                   & " of " & Step_Image (GS_Gnat2Why)
                   & ": " & Text_Of_Step (Step) & " ...");
      end if;

      case Step is
         when GS_ALI =>
            Compute_ALI_Information (Project_File, Proj, Status);
            if Status /= 0
              and then MMode = GPM_Check
            then
               Status := 0;
            end if;

         when GS_Gnat2Why =>
            Flow_Analysis_And_Proof (Project_File, Proj, Status);
            if Status /= 0
              and then MMode = GPM_Check
            then
               Status := 0;
            end if;

      end case;

      if Status /= 0 then
         Abort_With_Message
           ("gnatprove: error during " & Text_Of_Step (Step));
      end if;
   end Execute_Step;

   -----------------------------------
   -- Replace_Config_File_If_Needed --
   -----------------------------------

   function Replace_Config_File_If_Needed
     (Config_File : String;
      New_File    : String) return String
   is
      Handle : File_Type;

      procedure Copy_Replace_Line (Line : String);
      --  copy the given line over to Handle. If the line corresponds to the
      --  Runtime_library pattern, replace it by
      --    for Runtime_Library_Dir ("Ada") use ("dir");

      -----------------------
      -- Copy_Replace_Line --
      -----------------------

      procedure Copy_Replace_Line (Line : String) is
      begin
         if String_Utils.Starts_With (Line, "--RUNTIME_LIBRARY_DIR") then
            Put_Line
              (Handle,
               " for Runtime_Library_Dir (""Ada"") use """ & RTS_Dir.all &
                 """;");
         else
            Put_Line (Handle, Line);
         end if;
      end Copy_Replace_Line;

      procedure Copy_File is new For_Line_In_File (Copy_Replace_Line);

      --  beginning of processing for Replace_Config_File_If_Needed);

   begin
      if RTS_Dir = null or else RTS_Dir.all = "" then
         return Config_File;
      end if;
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

   ---------------------------
   -- Generate_SPARK_Report --
   ---------------------------

   procedure Generate_SPARK_Report
     (Obj_Dir  : String;
      Obj_Path : File_Array)
   is
      Obj_Dir_File : File_Type;
      Obj_Dir_Fn   : constant String :=
         Ada.Directories.Compose
            (Obj_Dir,
             "gnatprove.alfad");

      Success : Boolean;

      Args    : String_Lists.List := String_Lists.Empty_List;

   begin
      Create (Obj_Dir_File, Out_File, Obj_Dir_Fn);
      for Index in Obj_Path'Range loop
         Put_Line
            (Obj_Dir_File,
             Obj_Path (Index).Display_Full_Name);
      end loop;
      Close (Obj_Dir_File);

      Args.Append (Obj_Dir_Fn);
      if Assumptions then
         Args.Append ("--assumptions");
         if Limit_Subp /= null and then Limit_Subp.all /= "" then
            Args.Append ("--limit-subp=" & Limit_Subp.all);
         end if;
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

            if MMode /= GPM_Check
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

   -----------------------------
   -- Generate_Why3_Conf_File --
   -----------------------------

   procedure Generate_Why3_Conf_File
     (Gnatprove_Subdir : String)
   is
      File : File_Type;
      Filename : constant String :=
         Ada.Directories.Compose (Gnatprove_Subdir, "why3.conf");

      procedure Put_Keyval (Key : String; Value : String);
      procedure Put_Keyval (Key : String; Value : Integer);
      procedure Start_Section (Section : String);

      procedure Generate_Main_Section;
      procedure Generate_Altergo_Section;
      procedure Generate_CVC4_Section;
      procedure Generate_CVC4_CE_Section;

      --  The CVC4 options explained.
      --
      --  * lang=smt2
      --    we process SMTLIB2
      --
      --  * inst-when=full-last-call
      --    interleaves theory combination with quantifier instantiation,
      --    which can avoid matching loops (might return unsat faster)
      --
      --  * user-pat=trust
      --    trust the triggers we provide

      Common_CVC4_Options : constant String :=
        "--lang=smt2 " &
        "--inst-when=full-last-call " &
        "--user-pat=trust";

      ------------------------------
      -- Generate_Altergo_Section --
      ------------------------------

      procedure Generate_Altergo_Section is
         Altergo_Command : constant String := "alt-ergo -max-split 5 %f";
      begin
         Start_Section ("prover");
         if Steps /= 0 then
            Put_Keyval ("command",
                        Altergo_Command & " -steps " & Int_Image (Steps));
         else
            Put_Keyval ("command", Altergo_Command);
         end if;
         Put_Keyval ("driver",
                     Ada.Directories.Compose
                       (Why3_Drivers_Dir, "alt_ergo.drv"));
         Put_Keyval ("name", "altergo");
         Put_Keyval ("shortcut", "altergo");
         Put_Keyval ("version", "0.95");
      end Generate_Altergo_Section;

      ---------------------------
      -- Generate_CVC4_Section --
      ---------------------------

      procedure Generate_CVC4_Section is
         Command : constant String := "cvc4 " & Common_CVC4_Options;
      begin
         Start_Section ("prover");
         if Steps /= 0 then
            Put_Keyval ("command",
                        Command & " --rlimit=" & Int_Image (Steps * 10) &
                        " %f");
         else
            Put_Keyval ("command", Command & " %f");
         end if;
         Put_Keyval ("driver",
                     Ada.Directories.Compose
                       (Why3_Drivers_Dir, "cvc4_gnatprove.drv"));
         Put_Keyval ("name", "CVC4");
         Put_Keyval ("shortcut", "cvc4");
         Put_Keyval ("version", "1.3");
      end Generate_CVC4_Section;

      ------------------------------
      -- Generate_CVC4_CE_Section --
      ------------------------------

      procedure Generate_CVC4_CE_Section is
         --  The CVC4 options explained.
         --
         --  * finite-model-find
         --    resturn SAT on some quantified formulae
         --
         --  * macros-quant
         --    expand function definitions, and eliminate quantifiers, making
         --    it possible to return sat on more queries (instead of unknown)

         Command : constant String := "cvc4 " &
           Common_CVC4_Options &
           " --macros-quant" &
           " --finite-model-find";
      begin
         Start_Section ("prover");
         if Steps /= 0 then
            Put_Keyval ("command",
                        Command & " --rlimit=" & Int_Image (Steps) & " %f");
         else
            Put_Keyval ("command", Command & " %f");
         end if;
         Put_Keyval ("driver",
                     Ada.Directories.Compose
                       (Why3_Drivers_Dir, "cvc4_gnatprove.drv"));
         Put_Keyval ("name", "CVC4_CE");
         Put_Keyval ("shortcut", "cvc4_ce");
         Put_Keyval ("version", "1.3");
      end Generate_CVC4_CE_Section;

      ---------------------------
      -- Generate_Main_Section --
      ---------------------------

      procedure Generate_Main_Section is
      begin
         Start_Section ("main");
         Put_Keyval ("loadpath",
                     Ada.Directories.Compose (Why3_Dir, "theories"));
         Put_Keyval ("loadpath",
                     Ada.Directories.Compose (Why3_Dir, "modules"));
         Put_Keyval ("loadpath", Theories_Dir);
         Put_Keyval ("magic", 14);
         Put_Keyval ("memlimit", 0);
         Put_Keyval ("running_provers_max", 2);
      end Generate_Main_Section;

      ----------------
      -- Put_Keyval --
      ----------------

      procedure Put_Keyval (Key : String; Value : String) is
         use Ada.Strings.Unbounded;
         Value_Unb : Unbounded_String := To_Unbounded_String (Value);
      begin
         Replace (Value_Unb, "\", "\\");
         Put (File, Key);
         Put (File, " = """);
         Put (File, To_String (Value_Unb));
         Put_Line (File, """");
      end Put_Keyval;

      procedure Put_Keyval (Key : String; Value : Integer) is
      begin
         Put (File, Key);
         Put (File, " = ");
         Put_Line (File, Int_Image (Value));
      end Put_Keyval;

      -------------------
      -- Start_Section --
      -------------------

      procedure Start_Section (Section : String) is
      begin
         Put (File, "[");
         Put (File, Section);
         Put_Line (File, "]");
      end Start_Section;

      --  begin processing for Generate_Why3_Conf_File
   begin
      Create (File, Out_File, Filename);
      Generate_Main_Section;
      Generate_Altergo_Section;
      Generate_CVC4_Section;
      Generate_CVC4_CE_Section;

      Close (File);
   end Generate_Why3_Conf_File;

   ---------------------
   -- Set_Environment --
   ---------------------

   procedure Set_Environment is
      use Ada.Environment_Variables, GNAT.OS_Lib;

      Path_Val : constant String := Value ("PATH", "");
      Gpr_Val  : constant String := Value ("GPR_PROJECT_PATH", "");
      Libgnat  : constant String := Compose (Lib_Dir, "gnat");
      Sharegpr : constant String := Compose (Share_Dir, "gpr");

   begin
      --  Add <prefix>/libexec/spark2014/bin in front of the PATH
      Set ("PATH", Libexec_Bin_Dir & Path_Separator & Path_Val);

      --  Add <prefix>/lib/gnat & <prefix>/share/gpr in GPR_PROJECT_PATH
      --  so that project files installed with GNAT (not with SPARK)
      --  are found automatically, if any.

      Set ("GPR_PROJECT_PATH",
           Libgnat & Path_Separator & Sharegpr & Path_Separator & Gpr_Val);
   end Set_Environment;

   ----------
   -- Kill --
   ----------

   procedure Kill (P : in out Process_Descriptor) is
   begin
      Close (P);
   end Kill;

   ------------------------
   -- Non_Blocking_Spawn --
   ------------------------

   function Non_Blocking_Spawn
     (Command   : String;
      Arguments : String_Lists.List) return Process_Descriptor is
      Executable : constant String_Access :=
        GNAT.OS_Lib.Locate_Exec_On_Path (Command);
      Args       : constant GNAT.OS_Lib.Argument_List :=
        Argument_List_Of_String_List (Arguments);
      Proc       : Process_Descriptor;
   begin
      if Executable = null then
         Ada.Text_IO.Put_Line ("Could not find executable " & Command);
         GNAT.OS_Lib.OS_Exit (1);
      end if;
      Non_Blocking_Spawn
        (Proc,
         Executable.all,
         Args,
         Err_To_Out => True);
      return Proc;
   end Non_Blocking_Spawn;

   ------------------------------------
   -- Pass_Extra_Options_To_Gnat2why --
   ------------------------------------

   function Pass_Extra_Options_To_Gnat2why
      (Translation_Phase : Boolean;
       Obj_Dir           : String) return String is
      use Ada.Strings.Unbounded;
   begin
      --  In the translation phase, set a number of values

      if Translation_Phase then
         Gnat2Why_Args.Warning_Mode := Warning_Mode;
         Gnat2Why_Args.Global_Gen_Mode := False;
         Gnat2Why_Args.Debug_Mode := Debug;
         Gnat2Why_Args.Flow_Advanced_Debug := Flow_Extra_Debug;
         Gnat2Why_Args.Check_Mode := MMode = GPM_Check;
         Gnat2Why_Args.Flow_Analysis_Mode := MMode = GPM_Flow;
         Gnat2Why_Args.Prove_Mode := MMode = GPM_Prove;
         Gnat2Why_Args.Debug_Proof_Only := Configuration.Debug_Proof_Only;
         Gnat2Why_Args.Analyze_File := File_List;
         Gnat2Why_Args.Pedantic := Pedantic;
         Gnat2Why_Args.Ide_Mode := IDE_Progress_Bar;
         Gnat2Why_Args.Single_File := Only_Given;
         Gnat2Why_Args.Limit_Subp :=
           Ada.Strings.Unbounded.To_Unbounded_String (Limit_Subp.all);
         Gnat2Why_Args.Limit_Line :=
           Ada.Strings.Unbounded.To_Unbounded_String (Limit_Line.all);
         Gnat2Why_Args.Why3_Args := Compute_Why3_Args;
         Gnat2Why_Args.Report_Mode := Report;
         Gnat2Why_Args.Why3_Dir := To_Unbounded_String (Obj_Dir);

      --  In the globals generation phase, only set Global_Gen_Mode and
      --  debug flags

      else
         Gnat2Why_Args.Global_Gen_Mode := True;
         Gnat2Why_Args.Debug_Mode := Debug;
         Gnat2Why_Args.Flow_Advanced_Debug := Flow_Extra_Debug;
      end if;

      return Gnat2Why_Args.Set (Obj_Dir);
   end Pass_Extra_Options_To_Gnat2why;

   ---------------------
   -- Spawn_VC_Server --
   ---------------------

   function Spawn_VC_Server
     (Proj_Type : Project_Type)
      return Process_Descriptor is
      Args    : String_Lists.List := String_Lists.Empty_List;
      Cur     : constant String := Ada.Directories.Current_Directory;
      Id      : Process_Descriptor;
   begin
      Ada.Directories.Set_Directory (Proj_Type.Object_Dir.Display_Full_Name);
      Args.Append ("-j");
      Args.Append (Int_Image (Parallel));
      Args.Append ("--socket");
      Args.Append (Socket_Name.all);
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
            return "generation of Global contracts";

         when GS_Gnat2Why =>
            case MMode is
               when GPM_Check =>
                  return "checking of SPARK legality rules";
               when GPM_Flow =>
                  return "analysis of data and information flow";
               when GPM_Prove | GPM_All =>
                  return "flow analysis and proof";
            end case;
      end case;
   end Text_Of_Step;

   ----------------------
   -- Translate_To_Why --
   ----------------------

   procedure Flow_Analysis_And_Proof
      (Project_File     : String;
       Proj             : Project_Tree;
       Status           : out Integer)
   is
      use String_Lists;
      Cur     : Cursor := First (Cargs_List);
      Args    : String_Lists.List := Empty_List;
      Obj_Dir : constant String :=
         Proj.Root_Project.Object_Dir.Display_Full_Name;
      Opt_File : aliased constant String :=
         Pass_Extra_Options_To_Gnat2why
            (Translation_Phase => True,
             Obj_Dir           => Obj_Dir);
      Del_Succ : Boolean;
      Id        : Process_Descriptor;
   begin

      Generate_Why3_Conf_File (Obj_Dir);

      Args.Append ("--subdirs=" & String (Subdir_Name));
      Args.Append ("--restricted-to-languages=ada");
      Args.Append ("-s");

      if Minimal_Compile then
         Args.Append ("-m");
      end if;

      for File of File_List loop
         Args.Append (File);
      end loop;

      Args.Append ("-cargs:Ada");
      Args.Append ("-gnatc");              --  No object file generation
      Args.Prepend ("--complete-output");  --  Replay results if up-to-date

      Args.Append ("-gnates=" & Opt_File);

      while Has_Element (Cur) loop
         Args.Append (Element (Cur));
         Next (Cur);
      end loop;
      if RTS_Dir.all /= "" then
         Args.Append ("--RTS=" & RTS_Dir.all);
      end if;

      Id := Spawn_VC_Server (Proj.Root_Project);

      Call_Gprbuild (Project_File,
                     Gpr_Translation_Cnf_File,
                     Compose (Obj_Dir, Gnat2why_Cgpr),
                     Args,
                     Status);
      if Status = 0 and then not Debug then
         GNAT.OS_Lib.Delete_File (Opt_File, Del_Succ);
      end if;
      Kill (Id);
   end Flow_Analysis_And_Proof;

   Tree      : Project_Tree;
   --  GNAT project tree

   Proj_Type : Project_Type;
   --  GNAT project

--  Start processing for Gnatprove

begin
   Set_Environment;
   Read_Command_Line (Tree);
   Proj_Type := Root_Project (Tree);

   Execute_Step (GS_ALI, Project_File.all, Tree);
   Execute_Step (GS_Gnat2Why, Project_File.all, Tree);

   declare
      Obj_Path : constant File_Array :=
        Object_Path (Proj_Type, Recursive => True);
   begin
      Generate_SPARK_Report (Proj_Type.Object_Dir.Display_Full_Name, Obj_Path);
   end;
exception
   when Invalid_Project =>
      Abort_With_Message
         ("Error while loading project file: " & Project_File.all);
end Gnatprove;
