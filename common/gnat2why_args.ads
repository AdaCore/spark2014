------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          G N A T 2 W H Y _ A R G S                       --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2019, AdaCore                     --
--                Copyright (C) 2017-2019, Altran UK Limited                --
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

with Ada.Containers.Indefinite_Hashed_Maps;
with Ada.Strings.Hash;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with String_Utils;          use String_Utils;

package Gnat2Why_Args is

   --  This package defines and initializes extra options of gnat2why, that are
   --  not relevant to the GNAT frontend. It defines both the reading and the
   --  writing of these extra options. There are two ways to use it, depending
   --  on whether you are on the reading side (gnat2why) or the writing side
   --  (gnatprove).

   --  For reading the extra options, simply call "init". Now the global
   --  variables defined at the beginning of this package are set corresponding
   --  to the extra options.

   --  For writing extra options, set the global variables to the required
   --  values, and call "Set".

   --  These extra options are stored in a file that is passed to gnat2why
   --  using the extra switch "-gnates=<file>". See the body of this package
   --  for the format of this file, the spec only describes what is needed for
   --  interfacing.

   ---------------
   -- Constants --
   ---------------

   --  Name of the object sub-directory in which files are generated by
   --  GNATprove.

   Name_GNATprove : constant String := "gnatprove";

   --  Maximum range of values to unroll a FOR loop with static bounds and no
   --  loop (in)variant.

   Max_Loop_Unrolling : constant := 20;

   -------------
   -- Options --
   -------------

   --  Warning mode for gnat2why. This is identical to Opt.Warning_Mode for the
   --  compiler. We duplicate this type here to avoid a dependency on compiler
   --  units.

   type SPARK_Warning_Mode_Type is (SW_Suppress, SW_Normal, SW_Treat_As_Error);

   Warning_Mode : SPARK_Warning_Mode_Type := SW_Treat_As_Error;

   --  Global generation mode. In this mode, gnat2why generates cross-reference
   --  information in ALI files about globals accessed by subprograms.

   Global_Gen_Mode : Boolean := False;

   --  SPARK 2014 checking mode. In this mode, gnat2why checks that code marked
   --  with SPARK_Mode => True does not violate SPARK 2014 rules.

   Check_Mode : Boolean := False;

   --  Check All mode. In this mode, gnat2why will do flow analysis but only
   --  report check related messages.

   Check_All_Mode : Boolean := False;

   --  Flow Analysis mode. In this mode, gnat2why will do only flow analysis

   Flow_Analysis_Mode : Boolean := False;

   --  Prove mode. In this mode gnat2why will also perform flow analysis, but
   --  only report soundness-related messages. Note that Flow_Analysis_Mode and
   --  Prove_Mode are mutually exclusive.

   Prove_Mode : Boolean := False;

   --  Enable basic debugging for gnat2why. This will dump the CFG and PDG is
   --  dot format, and print the gnatwhy3 command line.

   Debug_Mode : Boolean := False;

   --  This will enable additional tracing output and will call graphviz on
   --  each dumped graph.

   Flow_Advanced_Debug : Boolean := False;

   --  The SPARK RM does not make global contracts optional, rather this is a
   --  liberty we have taken in this implementation of SPARK. This flag is
   --  controlled by the --no-global-generation switch and will make sure the
   --  absence of a global contract means the same thing as Global => null. By
   --  default, in gnat2why we synthesize global contracts.

   Flow_Generate_Contracts : Boolean := True;

   --  This will show termination status (as far as flow is concerned) for each
   --  subprogram with a warning or info message.

   Flow_Termination_Proof : Boolean := False;

   --  This debug flag will show all generated contracts in a human-readable
   --  form. The main use are a few tests where we want to observe that GG is
   --  working correctly.

   Flow_Show_GG : Boolean := False;

   --  Generate guards for axioms of functions to avoid having an unsound axiom
   --  when a function has an inconsistent contract.

   Proof_Generate_Guards : Boolean := True;

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

   Pedantic : Boolean := False;

   CWE : Boolean := False;  --  Issue CWE Ids in messages

   --  Set the report mode (only failing VCs, all VCs, details)

   type Report_Mode_Type is (GPR_Fail,
                             GPR_All,
                             GPR_Provers,
                             GPR_Statistics);
   --  The modes for reporting of VCs.
   --    GPR_Fail means that only unproved VCs will be reported
   --    GPR_All means that all VCs will be reported
   --    GPR_Provers prints in addition which prover(s) proved a proved check
   --    GPR_Statistics in addition prints maximum steps and timings for proved
   --    checks.

   Report_Mode : Report_Mode_Type := GPR_Fail;

   --  Limit analysis to the given units

   Limit_Units : Boolean := False;

   --  Limit analysis to this subprogram

   Limit_Subp : Unbounded_String := Null_Unbounded_String;

   --  Limit analysis to a selected region

   Limit_Region : Unbounded_String := Null_Unbounded_String;

   --  Limit analysis to this line

   Limit_Line : Unbounded_String := Null_Unbounded_String;

   --  The Why3 command will be run in this directory

   Why3_Dir : Unbounded_String := Null_Unbounded_String;

   --  If CP_Res_Dir is "null", then CodePeer processing will be disabled.
   --  Otherwise, CodePeer results will be in this directory.

   CP_Res_Dir : Unbounded_String := Null_Unbounded_String;

   --  IDE mode. Error messages may be formatted differently in this mode (e.g.
   --  JSON dict).

   Ide_Mode : Boolean := False;

   type File_Specific is record
      --  Generate warnings by generating VCs and calling provers. As it is
      --  costly, it is not enabled by default.
      Proof_Warnings    : Boolean;

      --  Do not inline local functions to prove their code in the calling
      --  context.
      No_Inlining       : Boolean;

      --  Issue info messages related to gnatprove usage
      Info_Messages     : Boolean;

      --  The cmd line args to be passed to gnatwhy3. In fact the "gnatwhy3"
      --  executable name is not hardcoded and is passed as a first argument
      --  of this list.

      Why3_Args         : String_Lists.List;

      --  Prevent loop unrolling
      No_Loop_Unrolling : Boolean;
   end record;

   package File_Specific_Maps is new Ada.Containers.Indefinite_Hashed_Maps
     (Key_Type        => String,
      Element_Type    => File_Specific,
      Hash            => Ada.Strings.Hash,
      Equivalent_Keys => "=",
      "="             => "=");

   File_Specific_Map : File_Specific_Maps.Map;

   function Proof_Warnings return Boolean;
   function No_Inlining return Boolean;
   function Info_Messages return Boolean;
   function No_Loop_Unrolling return Boolean;
   function Why3_Args return String_Lists.List;

   --------------------------------
   -- Procedures of this package --
   --------------------------------

   procedure Init (Args_File   : String;
                   Source_File : String);
   --  Read the extra options information and set the corresponding global
   --  variables above.
   --  @param Filename the filename to read the extra information from.
   --    Basically, you should pass Opt.SPARK_Switches_File_Name.all here. We
   --    want to avoid the dependency on Opt here, so you need to pass it
   --    yourself.

   function Set (Obj_Dir : String) return String;
   --  Assuming that the above global variables are set to meaningful values,
   --  Read them, store them into a file that gnat2why can read in later and
   --  return the file name.
   --  @param Obj_Dir the directory in which the file should be stored
   --  @return full name of the file that is to be passed to gnat2why using
   --    -gnates=<file>. The chosen file name will be identical for identical
   --    contents of the file.

private

   Local_Proof_Warnings    : Boolean := False;
   Local_No_Inlining       : Boolean := False;
   Local_Info_Messages     : Boolean := False;
   Local_No_Loop_Unrolling : Boolean := False;
   Local_Why3_Args         : String_Lists.List := String_Lists.Empty_List;

   function Proof_Warnings return Boolean is (Local_Proof_Warnings);
   function No_Inlining return Boolean is (Local_No_Inlining);
   function Info_Messages return Boolean is (Local_Info_Messages);
   function No_Loop_Unrolling return Boolean is (Local_No_Loop_Unrolling);
   function Why3_Args return String_Lists.List is (Local_Why3_Args);

end Gnat2Why_Args;
