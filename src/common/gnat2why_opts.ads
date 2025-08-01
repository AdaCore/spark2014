------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         G N A T 2 W H Y _ O P T S                        --
--                                                                          --
--                                  S p e c                                 --
--                                                                          --
--                     Copyright (C) 2010-2025, AdaCore                     --
--              Copyright (C) 2017-2025, Capgemini Engineering              --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnat2why is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  gnat2why;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

package Gnat2Why_Opts is

   --  This package defines extra options of gnat2why, that are not relevant to
   --  the GNAT frontend. It only implements the common parts of writing those
   --  options by gnatprove and reading them by gnat2why.

   --  These extra options are stored in a file that is passed to gnat2why
   --  using the extra switch "-gnates=<file>". See the body of this package
   --  for the format of this file, the spec only describes what is needed for
   --  interfacing.

   ------------------
   -- Option types --
   ------------------

   type SPARK_Warning_Mode_Type is (SW_Suppress, SW_Normal, SW_Treat_As_Error);
   --  Warning mode for gnat2why. This is identical to Opt.Warning_Mode for the
   --  compiler. We duplicate this type here to avoid a dependency on compiler
   --  units.

   --  Output mode for check messages
   type Output_Mode_Type is
     (GPO_Brief,          --  Output minimal information on one line
      GPO_Oneline,        --  Output all information on one line, to be used
      --  for regression tests and inside the IDE which is
      --  responsible for breaking the messages in relevant
      --  chunks.
      --
      GPO_Pretty_Simple,  --  Output information relevant for command-line
      --  usage, split here over multiple lines.
      --
      GPO_Pretty_Color);  --  Same as GPO_Pretty plus colored output

   subtype GPO_Pretty is
     Output_Mode_Type range GPO_Pretty_Simple .. GPO_Pretty_Color;

   type Report_Mode_Type is (GPR_Fail, GPR_All, GPR_Provers, GPR_Statistics);
   --  The modes for reporting of VCs.
   --    GPR_Fail means that only unproved VCs will be reported
   --    GPR_All means that all VCs will be reported
   --    GPR_Provers prints in addition which prover(s) proved a proved check
   --    GPR_Statistics in addition prints maximum steps and timings for proved
   --    checks.

private

   ------------------
   -- Option names --
   ------------------

   --  Extra options are passed from gnatprove to gnat2why in a JSON file. The
   --  following package contains names of the JSON fields.
   --
   --  Note: option names are intentionally kept as private and only accessible
   --  to children of this package so that neither gnatprove or gnat2why
   --  directly rely on them; instead, they should use the writing/reading
   --  routines, respectively.

   CWE_Name                     : constant String := "cwe";
   Check_Counterexamples_Name   : constant String := "check_counterexamples";
   Debug_Exec_RAC_Name          : constant String := "debug_exec_rac";
   GP_Mode_Name                 : constant String := "gp_mode";
   Debug_Mode_Name              : constant String := "debug";
   Exclude_Line_Name            : constant String := "exclude_line";
   File_Specific_Name           : constant String := "file_specific";
   Flow_Advanced_Debug_Name     : constant String := "flow_advanced_debug";
   Flow_Generate_Contracts_Name : constant String := "flow_generate_contracts";
   Flow_Show_GG_Name            : constant String := "flow_show_gg";
   Global_Gen_Mode_Name         : constant String := "global_gen_mode";
   Gnattest_Values_Name         : constant String := "gnattest_values";
   Ide_Mode_Name                : constant String := "ide_mode";
   Limit_Lines_Name             : constant String := "limit_lines";
   Limit_Name_Name              : constant String := "limit_name";
   Limit_Region_Name            : constant String := "limit_region";
   Limit_Subp_Name              : constant String := "limit_subp";
   Limit_Units_Name             : constant String := "limit_units";
   No_Inlining_Name             : constant String := "no_inlining";
   No_Loop_Unrolling_Name       : constant String := "no_loop_unrolling";
   Output_Mode_Name             : constant String := "output_mode";
   Parallel_Why3_Name           : constant String := "parallel_why3";
   Proof_Generate_Guards_Name   : constant String :=
     "proof_generate_axiom_guards";
   Proof_Warnings_Name          : constant String := "proof_warnings";
   Report_Mode_Name             : constant String := "report_mode";
   Warning_Mode_Name            : constant String := "warning_mode";
   Why3_Args_Name               : constant String := "why3_args";
   Why3_Dir_Name                : constant String := "why3_dir";
   Warning_Status_Name          : constant String := "warning_status";

end Gnat2Why_Opts;
