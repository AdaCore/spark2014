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
--  tools. It works in two steps:
--
--  1) Flow_Analysis_And_Proof
--     This step does all the SPARK analyses: flow analysis and proof. The tool
--     "gnat2why" is called on all units, translates the SPARK code to Why3
--     and calls gnatwhy3 to prove the generated VCs.
--  2) Call SPARK_Report. The previous step has generated extra information,
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
with Ada.Text_IO;
with Call;            use Call;
with Configuration;   use Configuration;
with GNAT.OS_Lib;
with Gnatprove_Build; use Gnatprove_Build;
with GNATCOLL.Tribooleans;
with GPR2;            use GPR2;
with GPR2.Path_Name;
with GPR2.Project.Tree;
with GPR2.Project.View;
with Spark_Report;
with String_Utils;    use String_Utils;
with VC_Kinds;        use VC_Kinds;

procedure Gnatprove with SPARK_Mode is

   Success_Exit_Code : Ada.Command_Line.Exit_Status := 0;
   --  This variable contains the exit code emitted by gnatprove in case of
   --  success. This variable is changed to indicate some error situations that
   --  are not signalled via the GNATprove_Failure exception.

   SPARK_Files : String_Lists.List;
   --  List of .spark files produced by Flow_Analysis_And_Proof, passed to
   --  Generate_SPARK_Report.

   procedure Generate_SPARK_Report
     (Tree : Project.Tree.Object; Errors : Boolean);
   --  Generate the SPARK report. Set Errors to True if previous phases
   --  contained errors.

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

   ---------------------------
   -- Generate_SPARK_Report --
   ---------------------------

   procedure Generate_SPARK_Report
     (Tree : Project.Tree.Object; Errors : Boolean)
   is
      Obj_Dir : constant String := Artifact_Dir (Tree).String_Value;
      Status  : Integer;
   begin
      Spark_Report.Generate_Report
        (Tree        => Tree,
         Out_Dir     => Obj_Dir,
         SPARK_Files => SPARK_Files,
         Has_Errors  => Errors,
         Status      => Status);

      if not Quiet and then Configuration.Mode /= GPM_Check then
         Ada.Text_IO.Put_Line
           ("Summary logged in " & SPARK_Report_File (Obj_Dir));
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

   Tree : Project.Tree.Object;
   --  GNAT project tree

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
            Create_Dir_And_Parents (View.Object_Directory);
         end if;
      end;
   end loop;

   declare
      --  These strings have to make sense when preceded by "error during".
      Phase_Text : constant String :=
        (case Configuration.Mode is
           when GPM_Check           =>
             "fast partial checking of SPARK legality rules",
           when GPM_Check_All       => "full checking of SPARK legality rules",
           when GPM_Flow            => "analysis of data and information flow",
           when GPM_Prove | GPM_All => "flow analysis and proof");
      Success    : Boolean;
   begin
      Flow_Analysis_And_Proof (Tree, SPARK_Files, Success);

      if not Success then
         Generate_SPARK_Report (Tree, Errors => True);
         Fail ("gnatprove: error during " & Phase_Text);
      end if;
   end;

   Generate_SPARK_Report (Tree, Errors => False);
   Cleanup (Tree, "", Success_Exit_Code);

exception
   when E : GNATprove_Failure =>
      Cleanup (Tree, Exception_Message (E), Exit_Code => 1);
   when E : GNATprove_Success =>
      pragma Assert (Exception_Message (E) = "");
      Cleanup (Tree, "", Exit_Code => Success_Exit_Code);
end Gnatprove;
