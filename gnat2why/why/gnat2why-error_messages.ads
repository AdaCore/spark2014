------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                 G N A T 2 W H Y _ E R R O R _ M E S S A G E S            --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2014-2019, AdaCore                     --
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

with Debug.Timing;        use Debug.Timing;
with Flow_Error_Messages; use Flow_Error_Messages;
with GNATCOLL.JSON;
with SPARK_Atree;         use SPARK_Atree;
with Types;               use Types;
with VC_Kinds;            use VC_Kinds;

package Gnat2Why.Error_Messages is

   type VC_Id is new Natural;

   function Register_VC
     (N      : Node_Id;
      Reason : VC_Kind;
      E      : Entity_Id)
      return VC_Id
   with Pre => Present (N) and then Present (E);
   --  @param N node at which the VC is located
   --  @param Reason VC kind
   --  @param E entity of the subprogram/package elaboration to which the VC
   --    belongs
   --  @return a fresh ID for this VC

   procedure Register_VC_Entity (E : Entity_Id);
   --  @param E entity of a subprogram/package which will be considered by
   --    proof. This is required to know the list of subprograms which don't
   --    have any VC associated with them. This is useful for assumptions.

   function Has_Registered_VCs return Boolean;
   --  Returns True iff the function Register_VC has been called

   procedure Load_Codepeer_Results;
   --  Load the CodePeer result file and store results. Can be queried with
   --  "CodePeer_Has_Proved" function.
   --  Skips loading if Codepeer processing is disabled (CP_Res_Dir set to
   --  null) or when no result file is found. "CodePeer_Has_Proved" will always
   --  return False in that case.

   function CodePeer_Has_Proved (Slc : Source_Ptr; Kind : VC_Kind)
                                 return Boolean;
   --  @param Slc a source location (possibly an sloc chain)
   --  @param Kind a VC kind
   --  @return True if we have received from codepeer the information that the
   --    check identified by (Slc, Kind) always succeeds; return False
   --    otherwise or if we are not sure
   --  It is OK to call this function even when Load_CodePeer_Results was not
   --  called before. The function will return "False" in that case.

   procedure Parse_Why3_Results (S : String; Timing : in out Time_Token);

   procedure Emit_Proof_Result
     (Node       : Node_Id;
      Id         : VC_Id;
      Kind       : VC_Kind;
      Proved     : Boolean;
      E          : Entity_Id;
      SF_Id      : Session_File_Base_ID;
      How_Proved : Prover_Category;
      Extra_Msg  : String := "";
      Tracefile  : String := "";
      Cntexmp    : GNATCOLL.JSON.JSON_Value := GNATCOLL.JSON.Create_Object;
      Check_Tree : GNATCOLL.JSON.JSON_Value := GNATCOLL.JSON.Create_Object;
      VC_File    : String := "";
      VC_Loc     : Node_Id := Empty;
      Stats      : Prover_Stat_Maps.Map := Prover_Stat_Maps.Empty_Map;
      Editor_Cmd : String := "");
   --  Register the VC identified by node and kind as proved. This will emit
   --  a message if needed and register the result in JSON output. @parameter
   --  How_Proved identifies the prover type (possible values currently are
   --  "codepeer", "interval" and "", the empty string meaning "some prover
   --  used by why3 backend".
   --  @parameter VC_Loc is the location of the verification check as opposed
   --  to @parameter Node which contains the location of the first failing part
   --  of a VC (raised as location for messages).

end Gnat2Why.Error_Messages;
