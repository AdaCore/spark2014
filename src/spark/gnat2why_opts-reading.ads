------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                 G N A T 2 W H Y _ O P T S . R E A D I N G                --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2021, AdaCore                     --
--                Copyright (C) 2017-2021, Altran UK Limited                --
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

with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with String_Utils;          use String_Utils;

package Gnat2Why_Opts.Reading is

   --  Maximum range of values to unroll a FOR loop with static bounds and no
   --  loop (in)variant.

   Max_Loop_Unrolling : constant := 20;

   --  Warning mode for gnat2why. This is identical to Opt.Warning_Mode for the
   --  compiler. We duplicate this type here to avoid a dependency on compiler
   --  units.

   Warning_Mode : SPARK_Warning_Mode_Type;

   --  Global generation mode. In this mode, gnat2why generates cross-reference
   --  information in ALI files about globals accessed by subprograms.

   Global_Gen_Mode : Boolean;

   --  SPARK 2014 checking mode. In this mode, gnat2why checks that code marked
   --  with SPARK_Mode => True does not violate SPARK 2014 rules.

   Check_Mode : Boolean;

   --  Check All mode. In this mode, gnat2why will do flow analysis but only
   --  report check related messages.

   Check_All_Mode : Boolean;

   --  Flow Analysis mode. In this mode, gnat2why will do only flow analysis

   Flow_Analysis_Mode : Boolean;

   --  Prove mode. In this mode gnat2why will also perform flow analysis, but
   --  only report soundness-related messages. Note that Flow_Analysis_Mode and
   --  Prove_Mode are mutually exclusive.

   Prove_Mode : Boolean;

   --  Enable basic debugging for gnat2why. This will dump the CFG and PDG is
   --  dot format, and print the gnatwhy3 command line.

   Debug_Mode : Boolean;

   --  This will enable additional tracing output and will call graphviz on
   --  each dumped graph.

   Flow_Advanced_Debug : Boolean;

   --  This will disable the simplification of trivial counterexamples in order
   --  to allow analysis of missing counterexamples.

   Debug_Trivial : Boolean;

   --  The SPARK RM does not make global contracts optional, rather this is a
   --  liberty we have taken in this implementation of SPARK. This flag is
   --  controlled by the --no-global-generation switch and will make sure the
   --  absence of a global contract means the same thing as Global => null. By
   --  default, in gnat2why we synthesize global contracts.

   Flow_Generate_Contracts : Boolean;

   --  This debug flag will show all generated contracts in a human-readable
   --  form. The main use are a few tests where we want to observe that GG is
   --  working correctly.

   Flow_Show_GG : Boolean;

   --  Generate guards for axioms of functions to avoid having an unsound axiom
   --  when a function has an inconsistent contract.

   Proof_Generate_Guards : Boolean;

   --  When Pedantic is True, issue warnings on features that could cause
   --  portability issues with other compilers than GNAT. For example, issue
   --  a warning when the Ada RM allows reassociation of operators in an
   --  expression (something GNAT never does), which could lead to different
   --  overflows, e.g. on
   --    A + B + C
   --  which is parsed as
   --    (A + B) + C
   --  but could be reassociated by another compiler as
   --    A + (B + C)

   Pedantic : Boolean;

   --  Issue CWE Ids in messages

   CWE : Boolean;

   --  Output mode for check messages (oneline or pretty)

   Output_Mode : Output_Mode_Type;

   --  Set the report mode (only failing VCs, all VCs, details)

   Report_Mode : Report_Mode_Type;

   --  Limit analysis to the given units

   Limit_Units : Boolean;

   --  Limit analysis to this subprogram

   Limit_Subp : Unbounded_String;

   --  Limit analysis to a selected region

   Limit_Region : Unbounded_String;

   --  Limit analysis to this line

   Limit_Line : Unbounded_String;

   --  The Why3 command will be run in this directory

   Why3_Dir : Unbounded_String;

   --  If CP_Res_Dir is "null", then CodePeer processing will be disabled.
   --  Otherwise, CodePeer results will be in this directory.

   CP_Res_Dir : Unbounded_String;

   --  IDE mode. Error messages may be formatted differently in this mode (e.g.
   --  JSON dict).

   Ide_Mode : Boolean;

   --  Generate warnings by generating VCs and calling provers. As it is
   --  costly, it is not enabled by default.

   Proof_Warnings : Boolean;

   --  Issue info messages related to gnatprove usage

   Info_Messages : Boolean;

   --  Do not inline local functions to prove their code in the calling
   --  context.

   No_Inlining : Boolean;

   --  The cmd line args to be passed to gnatwhy3. In fact the "gnatwhy3"
   --  executable name is not hardcoded and is passed as a first argument
   --  of this list.

   Why3_Args : String_Lists.List;

   --  Prevent loop unrolling

   No_Loop_Unrolling : Boolean;

   ---------------------------
   -- Loading option values --
   ---------------------------

   procedure Load (Args_File   : String;
                   Source_File : String)
   with Pre => Args_File /= "" and then Source_File /= "";
   --  Read the extra options information and set the corresponding global
   --  variables above.
   --  @param Args_File the filename to read the extra information from.
   --    Basically, you should pass Opt.SPARK_Switches_File_Name.all here. We
   --    want to avoid the dependency on Opt here, so you need to pass it
   --    yourself.
   --  @param Source_File key for the map with file-specific options

end Gnat2Why_Opts.Reading;
