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
with Ada.Containers.Hashed_Sets;
with Ada.Text_IO;
with Atree;                use Atree;
with Common_Containers;    use Common_Containers;
with Einfo;                use Einfo;
with Errout;               use Errout;
with Flow_Error_Messages;  use Flow_Error_Messages;
with GNATCOLL.JSON;
with Gnat2Why.Assumptions; use Gnat2Why.Assumptions;
with Gnat2Why.Nodes;       use Gnat2Why.Nodes;
with Osint;                use Osint;
with Sinfo;                use Sinfo;

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

   package Id_Sets is new Ada.Containers.Hashed_Sets
     (Element_Type        => VC_Id,
      Hash                => Hash,
      Equivalent_Elements => "=",
      "="                 => "=");

   package Ent_Id_Set_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Id,
      Element_Type    => Id_Sets.Set,
      Hash            => Node_Hash,
      Equivalent_Keys => "=",
      "="             => Id_Sets."=");

   procedure Add_Id_To_Entity (Id : VC_Id; E : Entity_Id);
   --  enter the VC_Id into the map from entities to Id_Sets

   procedure Mark_VC_As_Proved_For_Entity
     (Id   : VC_Id;
      Kind : VC_Kind;
      E    : Entity_Id);
   --  remove the VC_Id from the map from entities to Id_Sets

   function Proved_Message
     (Node : Node_Id;
      Kind : VC_Kind) return String;
   --  return the message string for a proved VC

   function Not_Proved_Message
     (Node : Node_Id;
      Kind : VC_Kind) return String;
   --  return the message string for an unproved VC

   VC_Table : Id_Maps.Map := Id_Maps.Empty_Map;
   --  This table maps ids to their VC_Info (entity and Ada node)

   VC_Set_Table : Ent_Id_Set_Maps.Map := Ent_Id_Set_Maps.Empty_Map;
   --  This table maps entities to the set of unproved VCs

   ----------------------
   -- Add_Id_To_Entity --
   ----------------------

   procedure Add_Id_To_Entity (Id : VC_Id; E : Entity_Id)
   is

      procedure Add_To_Set (Key : Entity_Id; S : in out Id_Sets.Set);

      ----------------
      -- Add_To_Set --
      ----------------

      procedure Add_To_Set (Key : Entity_Id; S : in out Id_Sets.Set) is
         pragma Unreferenced (Key);
      begin
         S.Include (Id);
      end Add_To_Set;

      use Ent_Id_Set_Maps;
      C : constant Cursor := VC_Set_Table.Find (E);
   begin
      if C /= No_Element then
         VC_Set_Table.Update_Element (C, Add_To_Set'Access);
      else
         VC_Set_Table.Insert (E, Id_Sets.To_Set (Id));
      end if;
   end Add_Id_To_Entity;

      -----------------------
      -- Emit_Proof_Result --
      -----------------------

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
        (if Proved then Proved_Message (Node, Kind)
         else Not_Proved_Message (Node, Kind)) &
        Extra_Msg & (if VC_File /= "" then ", vc file: " & VC_File else "");
   begin
      Error_Msg_Proof
        (Node,
         Msg,
         Proved,
         To_Tag (Kind),
         Place_First => Locate_On_First_Token (Kind),
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

   ----------------------------------
   -- Mark_VC_As_Proved_For_Entity --
   ----------------------------------

   procedure Mark_VC_As_Proved_For_Entity
     (Id   : VC_Id;
      Kind : VC_Kind;
      E    : Entity_Id) is

      Removal_Made_Set_Empty : Boolean := False;

      procedure Remove_Id (Key : Entity_Id; S : in out Id_Sets.Set);

      ---------------
      -- Remove_Id --
      ---------------

      procedure Remove_Id (Key : Entity_Id; S : in out Id_Sets.Set) is
         pragma Unreferenced (Key);
      begin
         S.Delete (Id);
         if S.Is_Empty then
            Removal_Made_Set_Empty := True;
         end if;
      end Remove_Id;

      use Ent_Id_Set_Maps;
      C : constant Cursor := VC_Set_Table.Find (E);
   begin

      --  ??? little trick; loop invariant assertions cannot be simply removed,
      --  because there are two of them with the same ID. We fix this by only
      --  counting the "preservation" one, and ignore the "init" one.

      if Kind = VC_Loop_Invariant_Init then
         return;
      end if;
      pragma Assert (C /= No_Element);
      VC_Set_Table.Update_Element (C, Remove_Id'Access);
      if Removal_Made_Set_Empty then
         Register_Proof_Claims (E);
      end if;
   end Mark_VC_As_Proved_For_Entity;

   ------------------------
   -- Not_Proved_Message --
   ------------------------

   function Not_Proved_Message
     (Node : Node_Id;
      Kind : VC_Kind) return String is
   begin
      case Kind is
         when VC_Division_Check            =>
            return "divide by zero might fail";
         when VC_Index_Check               =>
            return "array index check might fail";
         when VC_Overflow_Check            =>
            return "overflow check might fail";
         when VC_Range_Check               =>
            return "range check might fail";
         when VC_Length_Check              =>
            return "length check might fail";
         when VC_Discriminant_Check        =>
            return "discriminant check might fail";
         when VC_Tag_Check                 =>
            return "tag check might fail";
         when VC_Initial_Condition         =>
            return "initial condition might fail";
         when VC_Default_Initial_Condition =>
            return "default initial condition might fail";
         when VC_Precondition              =>
            if Nkind (Node) in N_Function_Call | N_Procedure_Call_Statement
              and then No_Return (Entity (Name (Node)))
            then
               return
                 "call to nonreturning subprogram might be executed";
            else
               return "precondition might fail";
            end if;
         when VC_Precondition_Main         =>
            return "precondition of main program might fail";
         when VC_Postcondition             =>
            return "postcondition might fail";
         when VC_Refined_Post              =>
            return "refined postcondition might fail";
         when VC_Contract_Case             =>
            return "contract case might fail";
         when VC_Disjoint_Contract_Cases   =>
            return "contract cases might not be disjoint";
         when VC_Complete_Contract_Cases   =>
            return "contract cases might not be complete";
         when VC_Loop_Invariant            =>
            return "loop invariant might fail";
         when VC_Loop_Invariant_Init       =>
            return "loop invariant might fail in first iteration";
         when VC_Loop_Invariant_Preserv    =>
            return "loop invariant might fail after first iteration";
         when VC_Loop_Variant              =>
            return "loop variant might fail";
         when VC_Assert                    =>
            return "assertion might fail";
         when VC_Raise                     =>
            return "exception might be raised";
         when VC_Weaker_Pre                =>
            return "precondition might be stronger than "
              & "class-wide precondition";
         when VC_Trivial_Weaker_Pre        =>
            return "precondition is stronger than the default "
              & "class-wide precondition of True";
         when VC_Stronger_Post             =>
            return "postcondition might be weaker than "
              & "class-wide postcondition";
         when VC_Weaker_Classwide_Pre      =>
            return
              "class-wide precondition might be stronger than overridden one";
         when VC_Stronger_Classwide_Post   =>
            return
              "class-wide postcondition might be weaker than overridden one";
      end case;
   end Not_Proved_Message;

   ------------------------
   -- Parse_Why3_Results --
   ------------------------

   procedure Parse_Why3_Results (S : String) is

      --  See the file gnat_report.mli for a description of the format that we
      --  parse here

      use GNATCOLL.JSON;

      procedure Handle_Result (V : JSON_Value);
      procedure Handle_Error (Msg : String; Internal : Boolean);

      ------------------
      -- Handle_Error --
      ------------------

      procedure Handle_Error (Msg : String; Internal : Boolean) is
      begin
         if Internal then
            Ada.Text_IO.Put_Line ("Internal error");
            Ada.Text_IO.Put_Line (Msg);
            Exit_Program (E_Abort);
         else
            Ada.Text_IO.Put ("gnatprove: ");
            Ada.Text_IO.Put_Line (Msg);
            raise Terminate_Program;
         end if;
      end Handle_Error;

      -------------------
      -- Handle_Result --
      -------------------

      procedure Handle_Result (V : JSON_Value) is
         Id        : constant VC_Id := VC_Id (Integer'(Get (Get (V, "id"))));
         VC        : constant VC_Info := VC_Table.Element (Id);
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
         if  Proved then
            Mark_VC_As_Proved_For_Entity (Id, Kind, VC.Entity);
         end if;
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
         Results  : constant JSON_Array := Get (Get (File, "results"));
      begin
         if Has_Field (File, "error") then
            declare
               Msg : constant String := Get (Get (File, "error"));
               Internal : constant Boolean :=
                 (if Has_Field (File, "internal") then
                       Get (Get (File, "internal"))
                  else False);
            begin
               Handle_Error (Msg, Internal);
            end;
         end if;
         for Index in 1 .. Length (Results) loop
            Handle_Result (Get (Results, Index));
         end loop;
      end;
   exception
      when Invalid_JSON_Stream =>
         --  something bad happened, output gnatwhy3 error as is
         Handle_Error (S, Internal => True);
   end Parse_Why3_Results;

   --------------------
   -- Proved_Message --
   --------------------

   function Proved_Message
     (Node : Node_Id;
      Kind : VC_Kind) return String is
   begin
      case Kind is
         when VC_Division_Check            => return "division check proved";
         when VC_Index_Check               => return "index check proved";
         when VC_Overflow_Check            => return "overflow check proved";
         when VC_Range_Check               => return "range check proved";
         when VC_Length_Check              => return "length check proved";
         when VC_Discriminant_Check        =>
            return "discriminant check proved";
         when VC_Tag_Check                 =>
            return "tag check proved";

         when VC_Initial_Condition         =>
            return "initial condition proved";
         when VC_Default_Initial_Condition =>
            return "default initial condition proved";
         when VC_Precondition              =>
            if Nkind (Node) in N_Function_Call | N_Procedure_Call_Statement
              and then No_Return (Entity (Name (Node)))
            then
               return "call to nonreturning procedure never executed";
            else
               return "precondition proved";
            end if;
         when VC_Precondition_Main         =>
            return "precondition of main program proved";
         when VC_Postcondition             => return "postcondition proved";
         when VC_Refined_Post              => return "refined post proved";
         when VC_Contract_Case             => return "contract case proved";
         when VC_Disjoint_Contract_Cases   =>
            return "disjoint contract cases proved";
         when VC_Complete_Contract_Cases   =>
            return "complete contract cases proved";
         when VC_Loop_Invariant            =>
            return "loop invariant proved";
         when VC_Loop_Invariant_Init       =>
            return "loop invariant initialization proved";
         when VC_Loop_Invariant_Preserv    =>
            return "loop invariant preservation proved";
         when VC_Loop_Variant              => return "loop variant proved";
         when VC_Assert                    => return "assertion proved";
         when VC_Raise                     =>
            return "raise statement proved unreachable";
         when VC_Weaker_Pre                =>
            return "precondition is weaker than class-wide precondition";
         when VC_Trivial_Weaker_Pre        =>
            return "precondition is always True";
         when VC_Stronger_Post             =>
            return "postcondition is stronger than class-wide postcondition";
         when VC_Weaker_Classwide_Pre      =>
            return "class-wide precondition is weaker than overridden one";
         when VC_Stronger_Classwide_Post   =>
            return "class-wide postcondition is stronger than overridden one";
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
      Add_Id_To_Entity (Tmp, E);
      return Tmp;
   end Register_VC;

   ------------
   -- To_Tag --
   ------------

   function To_Tag (Kind : VC_Kind) return String is
   begin
      return
      (case Kind is
         when VC_Division_Check            => "division_check",
         when VC_Index_Check               => "index_check",
         when VC_Overflow_Check            => "overflow_check",
         when VC_Range_Check               => "range_check",
         when VC_Length_Check              => "length_check",
         when VC_Discriminant_Check        => "discriminant_check",
         when VC_Tag_Check                 => "tag_check",
         when VC_Default_Initial_Condition => "default_initial_condition",
         when VC_Initial_Condition         => "initial_condition",
         when VC_Precondition              => "precondition",
         when VC_Precondition_Main         => "precondition_main",
         when VC_Postcondition             => "postcondition",
         when VC_Refined_Post              => "refined_post",
         when VC_Contract_Case             => "contract_case",
         when VC_Disjoint_Contract_Cases   => "disjoint_contract_cases",
         when VC_Complete_Contract_Cases   => "complete_contract_cases",
         when VC_Loop_Invariant            => "loop_invariant",
         when VC_Loop_Invariant_Init       => "loop_invariant_initialization",
         when VC_Loop_Invariant_Preserv    => "loop_invariant_preservation",
         when VC_Loop_Variant              => "loop_variant",
         when VC_Assert                    => "assertion",
         when VC_Raise                     => "raise_statement",
         when VC_Weaker_Pre                => "weaker_pre",
         when VC_Trivial_Weaker_Pre        => "trivial_weaker_pre",
         when VC_Stronger_Post             => "stronger_post",
         when VC_Weaker_Classwide_Pre      => "weaker_classwide_pre",
         when VC_Stronger_Classwide_Post   => "stronger_classwide_post"
      );
   end To_Tag;

end Gnat2Why.Error_Messages;
