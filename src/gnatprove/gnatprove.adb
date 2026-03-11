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
with Ada.Exceptions;  use Ada.Exceptions;
with Ada.Text_IO;     use Ada.Text_IO;
with Call;            use Call;
with Configuration;   use Configuration;
with GNAT.OS_Lib;
with GNAT.Strings;    use GNAT.Strings;
with Gnatprove_Build; use Gnatprove_Build;
with Gnat2Why_Opts;
with GNATCOLL.JSON;   use GNATCOLL.JSON;
with GNATCOLL.Tribooleans;
with GNATCOLL.Utils;  use GNATCOLL.Utils;
with GNATCOLL.VFS;    use GNATCOLL.VFS;
with GPR2;            use GPR2;
with GPR2.Path_Name;
with GPR2.Project.Attribute;
with GPR2.Project.Tree;
with GPR2.Project.View;
with String_Utils;    use String_Utils;
with VC_Kinds;        use VC_Kinds;

procedure Gnatprove with SPARK_Mode is

   type Gnatprove_Step is (GS_Data_Representation, GS_Gnat2Why);
   --  ??? No need for this plan stuff anymore

   type Plan_Type is array (Positive range <>) of Gnatprove_Step;

   Success_Exit_Code : Ada.Command_Line.Exit_Status := 0;
   --  This variable contains the exit code emitted by gnatprove in case of
   --  success. This variable is changed to indicate some error situations that
   --  are not signalled via the GNATprove_Failure exception.

   procedure Call_Gprbuild
     (Project_File : String;
      Tree         : Project.Tree.Object;
      Args         : in out String_Lists.List;
      Status       : out Integer);
   --  Call gprbuild with the given arguments. DB_Dir is the directory
   --  which contains the information to configure gprbuild correctly.

   procedure Compute_Data_Representation
     (Project_File : String; Tree : Project.Tree.Object; Status : out Integer);
   --  Compute data representation for all source units, using gprbuild

   procedure Execute_Step
     (Plan         : Plan_Type;
      Step         : Positive;
      Project_File : String;
      Tree         : Project.Tree.Object);

   procedure Generate_SPARK_Report
     (Tree : Project.Tree.Object; Errors : Boolean);
   --  Generate the SPARK report. Set Errors to True if previous phases
   --  contained errors.

   function Text_Of_Step (Step : Gnatprove_Step) return String;

   procedure Set_Environment;
   --  Set the environment before calling other tools.
   --  In particular, add any needed directories in the PATH and
   --  GPR_PROJECT_PATH env vars.

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
     (Project_File : String;
      Tree         : Project.Tree.Object;
      Args         : in out String_Lists.List;
      Status       : out Integer)
   is
      Obj_Dir     : constant String :=
        Ada.Directories.Full_Name
          (Artifact_Dir (Tree).Virtual_File.Display_Full_Name);
      Output_Name : constant String :=
        Ada.Directories.Compose
          (Obj_Dir, "data_representation_generation", "log");
   begin
      Args.Append ("--restricted-to-languages=ada");

      --  We explicitly set the target (which has been already figured out by
      --  the GPR machinery). This way gprbuild will only call gprconfig once:
      --  to generate a configuration for that specific target. Otherwise
      --  gprbuild would make an extra call to gprconfig, just to find the
      --  target.

      Args.Append ("--target=" & String (Tree.Target));

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

      Args.Append ("-S");  --  Stop after compilation and do not assemble
      Args.Append ("-gnatR2js");  --  Generate data representation files
      Args.Append ("-gnatws");    --  Suppress all warnings
      Args.Append ("-gnatx");     --  Suppress cross-ref information

      if GnateT_Switch /= null and then GnateT_Switch.all /= "" then
         Args.Append (Configuration.GnateT_Switch.all);
      end if;

      Args.Append ("-gnatis");  --  Suppress all info messages

      Call_With_Status
        (Command     => "gprbuild",
         Arguments   => Args,
         Status      => Status,
         Output_Name => Output_Name,
         Verbose     => Verbose);

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

      Call_Gprbuild (Project_File, Tree, Args => Args, Status => Status);

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

         when GS_Gnat2Why            =>
            Flow_Analysis_And_Proof (Tree, Status);
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

   ---------------------------
   -- Generate_SPARK_Report --
   ---------------------------

   procedure Generate_SPARK_Report
     (Tree : Project.Tree.Object; Errors : Boolean)
   is
      Obj_Dir    : constant String :=
        Artifact_Dir (Tree).Virtual_File.Display_Full_Name;
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
         --  Strip path and extension from the command name
         Append
           (Cmdline_JSON,
            Create
              (Ada.Directories.Base_Name
                 (Ada.Directories.Simple_Name (Command_Name))));
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

   Tree : Project.Tree.Object;
   --  GNAT project tree

   --  Start processing for Gnatprove

begin
   Set_Environment;
   Read_Command_Line (Tree);

   if not Artifact_Dir (Tree).Is_Defined then
      Fail
        ("Error while loading project file: "
         & CL_Switches.P.all
         & ": "
         & "could not determine working directory");
   end if;
   Create_Dir_And_Parents (Artifact_Dir (Tree).Virtual_File);

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
      Plan : constant Plan_Type := [GS_Data_Representation, GS_Gnat2Why];
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
