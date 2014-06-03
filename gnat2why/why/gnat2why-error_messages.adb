------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                 G N A T 2 W H Y _ E R R O R _ M E S S A G E S            --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2014, AdaCore                        --
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
with Ada.Containers.Hashed_Maps;
with Ada.Text_IO;

with GNATCOLL.JSON;

with Atree;               use Atree;
with Errout;              use Errout;
with Flow_Error_Messages; use Flow_Error_Messages;
with Osint;               use Osint;

with Gnat2Why.Nodes;      use Gnat2Why.Nodes;

package body Gnat2Why.Error_Messages is

   VC_Id_Counter : VC_Id := 0;

   type VC_Info is record
      Node   : Node_Id;
      Entity : Entity_Id;
   end record;

   function Hash (X : VC_Id) return Ada.Containers.Hash_Type is
      (Ada.Containers.Hash_Type (X));

   package Id_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => VC_Id,
      Element_Type    => VC_Info,
      Hash            => Hash,
      Equivalent_Keys => "=",
      "="             => "=");

   VC_Table : Id_Maps.Map := Id_Maps.Empty_Map;

   procedure Emit_Proof_Result
     (Node       : Node_Id;
      Kind       : VC_Kind;
      Proved     : Boolean;
      E          : Entity_Id;
      Extra_Msg  : String := "";
      Tracefile  : String := "";
      VC_File    : String := "";
      Editor_Cmd : String := "") is
      Msg : constant String :=
        (if Proved then Proved_Message (Kind) else Not_Proved_Message (Kind)) &
        Extra_Msg;
   begin
      Error_Msg_Proof
        (Node,
         Msg,
         Proved,
         To_Tag (Kind),
         Place_First => Is_Assertion_Kind (Kind),
         Tracefile   => Tracefile,
         VC_File     => VC_File,
         Editor_Cmd  => Editor_Cmd,
         E           => E);
   end Emit_Proof_Result;

   ------------------------
   -- Has_Registered_VCs --
   ------------------------

   function Has_Registered_VCs return Boolean is
   begin
      return not (VC_Table.Is_Empty);
   end Has_Registered_VCs;

   ------------------------
   -- Not_Proved_Message --
   ------------------------

   function Not_Proved_Message (Kind : VC_Kind) return String is
   begin
      case Kind is
         when VC_Division_Check          =>
            return "divide by zero might fail";
         when VC_Index_Check             =>
            return "array index check might fail";
         when VC_Overflow_Check          =>
            return "overflow check might fail";
         when VC_Range_Check             =>
            return "range check might fail";
         when VC_Length_Check            =>
            return "length check might fail";
         when VC_Discriminant_Check      =>
            return "discriminant check might fail";
         when VC_Initial_Condition       =>
            return "initial condition might fail";
         when VC_Precondition            =>
            return "precondition might fail";
         when VC_Precondition_Main       =>
            return "precondition of main program might fail";
         when VC_Postcondition           =>
            return "postcondition might fail";
         when VC_Refined_Post            =>
            return "refined postcondition might fail";
         when VC_Contract_Case           =>
            return "contract case might fail";
         when VC_Disjoint_Contract_Cases =>
            return "contract cases might not be disjoint";
         when VC_Complete_Contract_Cases =>
            return "contract cases might not be complete";
         when VC_Loop_Invariant          =>
            return "loop invariant might fail";
         when VC_Loop_Invariant_Init     =>
            return "loop invariant might fail in first iteration";
         when VC_Loop_Invariant_Preserv  =>
            return "loop invariant might fail after first iteration";
         when VC_Loop_Variant            =>
            return "loop variant might fail";
         when VC_Assert                  =>
            return "assertion might fail";
         when VC_Raise                   =>
            return "exception might be raised";
      end case;
   end Not_Proved_Message;

   ------------------------
   -- Parse_Why3_Results --
   ------------------------

   procedure Parse_Why3_Results (S : String) is

      use GNATCOLL.JSON;

      procedure Handle_Result (V : JSON_Value);

      -------------------
      -- Handle_Result --
      -------------------

      procedure Handle_Result (V : JSON_Value) is
         Id        : constant Integer := Get (Get (V, "id"));
         VC        : constant VC_Info := VC_Table.Element (VC_Id (Id));
         Kind      : constant VC_Kind :=
           VC_Kind'Value (Get (Get (V, "reason")));
         Proved    : constant Boolean := Get (Get (V, "result"));
         Extra     : constant Node_Id :=
           Node_Id (Integer'(Get (Get (V, "extra_info"))));
         Extra_Text : constant String :=
           (if not Proved and then Present (Extra) then
                 String_Of_Node (Extra)
            else "");
         Extra_Msg  : constant String :=
           (if Extra_Text /= "" then ", requires ~"
            else "");
         Node   : constant Node_Id :=
           (if Present (Extra) then Extra else VC.Node);
         Tracefile : constant String :=
           (if Has_Field (V, "tracefile") then Get (Get (V, "tracefile"))
            else "");
         VC_File : constant String :=
           (if Has_Field (V, "vc_file") then Get (Get (V, "vc_file"))
            else "");
         Editor_Cmd : constant String :=
           (if Has_Field (V, "editor_cmd") then Get (Get (V, "editor_cmd"))
            else "");
      begin
         Errout.Error_Msg_String (1 .. Extra_Text'Length) := Extra_Text;
         Errout.Error_Msg_Strlen := Extra_Text'Length;
         Emit_Proof_Result
           (Node       => Node,
            Kind       => Kind,
            Proved     => Proved,
            E          => VC.Entity,
            Tracefile  => Tracefile,
            VC_File    => VC_File,
            Editor_Cmd => Editor_Cmd,
            Extra_Msg  => Extra_Msg);
      end Handle_Result;

   begin
      declare
         File : constant JSON_Value := Read (S, "");
         Results  : constant JSON_Array := Get (File);
      begin
         for Index in 1 .. Length (Results) loop
            Handle_Result (Get (Results, Index));
         end loop;
      end;
   exception
      when Invalid_JSON_Stream =>
         --  something bad happened, output gnatwhy3 error as is

         Ada.Text_IO.Put_Line ("Internal error");
         Ada.Text_IO.Put_Line (S);
         Exit_Program (E_Abort);
   end Parse_Why3_Results;

   --------------------
   -- Proved_Message --
   --------------------

   function Proved_Message (Kind : VC_Kind) return String is
   begin
      case Kind is
         when VC_Division_Check          => return "division check proved";
         when VC_Index_Check             => return "index check proved";
         when VC_Overflow_Check          => return "overflow check proved";
         when VC_Range_Check             => return "range check proved";
         when VC_Length_Check            => return "length check proved";
         when VC_Discriminant_Check      => return "discriminant check proved";
         when VC_Initial_Condition       => return "initial condition proved";
         when VC_Precondition            => return "precondition proved";
         when VC_Precondition_Main       =>
            return "precondition of main program proved";
         when VC_Postcondition           => return "postcondition proved";
         when VC_Refined_Post            => return "refined post proved";
         when VC_Contract_Case           => return "contract case proved";
         when VC_Disjoint_Contract_Cases =>
            return "disjoint contract cases proved";
         when VC_Complete_Contract_Cases =>
            return "complete contract cases proved";
         when VC_Loop_Invariant          =>
            return "loop invariant proved";
         when VC_Loop_Invariant_Init     =>
            return "loop invariant initialization proved";
         when VC_Loop_Invariant_Preserv  =>
            return "loop invariant preservation proved";
         when VC_Loop_Variant            => return "loop variant proved";
         when VC_Assert                  => return "assertion proved";
         when VC_Raise                   =>
            return "raise statement proved unreachable";
      end case;
   end Proved_Message;

   --------------
   -- Register --
   --------------

   function Register_VC (N : Node_Id; E : Entity_Id) return VC_Id is
      Tmp : constant VC_Id := VC_Id_Counter;
   begin
      VC_Table.Insert (Tmp, VC_Info'(N, E));
      VC_Id_Counter := VC_Id_Counter + 1;
      return Tmp;
   end Register_VC;

   ------------
   -- To_Tag --
   ------------

   function To_Tag (Kind : VC_Kind) return String is
   begin
      return
      (case Kind is
         when VC_Division_Check          => "division_check",
         when VC_Index_Check             => "index_check",
         when VC_Overflow_Check          => "overflow_check",
         when VC_Range_Check             => "range_check",
         when VC_Length_Check            => "length_check",
         when VC_Discriminant_Check      => "discriminant_check",
         when VC_Initial_Condition       => "initial_condition",
         when VC_Precondition            => "precondition",
         when VC_Precondition_Main       => "precondition_main",
         when VC_Postcondition           => "postcondition",
         when VC_Refined_Post            => "refined_post",
         when VC_Contract_Case           => "contract_case",
         when VC_Disjoint_Contract_Cases => "disjoint_contract_cases",
         when VC_Complete_Contract_Cases => "complete_contract_cases",
         when VC_Loop_Invariant          => "loop_invariant",
         when VC_Loop_Invariant_Init     => "loop_invariant_initialization",
         when VC_Loop_Invariant_Preserv  => "loop_invariant_preservation",
         when VC_Loop_Variant            => "loop_variant",
         when VC_Assert                  => "assertion",
         when VC_Raise                   => "raise_statement");
   end To_Tag;

end Gnat2Why.Error_Messages;
