------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                 G N A T 2 W H Y _ E R R O R _ M E S S A G E S            --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2014-2022, AdaCore                     --
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

with Ada.Containers;
with Debug.Timing;              use Debug.Timing;
with Flow_Error_Messages;       use Flow_Error_Messages;
with GNATCOLL.JSON;
with SPARK_Atree;               use SPARK_Atree;
with SPARK_Util;                use SPARK_Util;
with Types;                     use Types;
with VC_Kinds;                  use VC_Kinds;

package Gnat2Why.Error_Messages is

   type VC_Id is new Natural;

   function Register_VC
     (N               : Node_Id;
      Reason          : VC_Kind;
      E               : Entity_Id;
      Check_Info      : Check_Info_Type;
      Present_In_Why3 : Boolean := True)
      return VC_Id
   with Pre => Present (N) and then Present (E);
   --  @param N node at which the VC is located
   --  @param Reason VC kind
   --  @param E entity of the subprogram/package elaboration to which the VC
   --    belongs
   --  @param Info additional information on the check
   --  @param Present_In_Why3 if the VC actually appears in the Why3. This
   --    Boolean explains the difference between the functions
   --    Num_Registered_VCs and Num_Registered_VCs_In_Why3 below.
   --  @return a fresh ID for this VC

   procedure Register_VC_Entity (E : Entity_Id);
   --  @param E entity of a subprogram/package which will be considered by
   --    proof. This is required to know the list of subprograms which don't
   --    have any VC associated with them. This is useful for assumptions.

   function Num_Registered_VCs return Ada.Containers.Count_Type;
   --  Returns the number of registered VCs

   function Num_Registered_VCs_In_Why3 return Natural;
   --  VCs that actually appear in the Why3 file(s)

   procedure Parse_Why3_Results (Fn : String; Timing : in out Time_Token);

   generic
      Verb : String;
      Prefix : String := "";
      Suffix : String := "";
   function VC_Message (Node : Node_Id; Kind : VC_Kind) return String;
   --  Return the message string for a VC. This is used for proved checks and
   --  for justified checks

   procedure Emit_Proof_Result
     (Node          : Node_Id;
      Id            : VC_Id;
      Kind          : VC_Kind;
      Proved        : Boolean;
      E             : Entity_Id;
      SD_Id         : Session_Dir_Base_ID;
      How_Proved    : Prover_Category;
      Check_Info    : Check_Info_Type;
      Extra_Msg     : String := "";
      Explanation   : String := "";
      Cntexmp       : GNATCOLL.JSON.JSON_Value := GNATCOLL.JSON.Create_Object;
      Verdict       : Cntexmp_Verdict := (others => <>);
      Check_Tree    : GNATCOLL.JSON.JSON_Value := GNATCOLL.JSON.Create_Object;
      VC_File       : String := "";
      VC_Loc        : Node_Id := Empty;
      Stats         : Prover_Stat_Maps.Map := Prover_Stat_Maps.Empty_Map;
      Editor_Cmd    : String := "";
      Fuzzing_Used  : Boolean := False;
      Print_Fuzzing : Boolean := False);
   --  Register the VC identified by node and kind as proved. This will emit
   --  a message if needed and register the result in JSON output. @parameter
   --  How_Proved identifies the prover type (possible values currently are
   --  "interval" and "", the empty string meaning "some prover used by why3
   --  backend".
   --  @parameter VC_Loc is the location of the verification check as opposed
   --  to @parameter Node which contains the location of the first failing part
   --  of a VC (raised as location for messages).
   --  @parameter Fuzzing_Used indicates wether the counterexample used to
   --  reach Verdict comes for the fuzzer
   --  @parameter Print_Fuzzing marks if the counterexample found by the fuzzer
   --  should be printed

   procedure Emit_Static_Proof_Result
     (Node        : Node_Id;
      Kind        : VC_Kind;
      Proved      : Boolean;
      E           : Entity_Id;
      Explanation : String := "");
   --  Register a new VC and save it as proved (or not proved depending on
   --  Proved argument). This function is similar to calling Register_VC, then
   --  Emit_Proof_Result.

end Gnat2Why.Error_Messages;
