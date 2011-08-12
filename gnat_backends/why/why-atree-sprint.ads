------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                     W H Y - A T R E E - S P R I N T                      --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
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

with Outputs;             use Outputs;
with Why.Atree.Traversal; use Why.Atree.Traversal;
with Why.Atree.Tables;    use Why.Atree.Tables;
with Why.Ids;             use Why.Ids;

package Why.Atree.Sprint is

   --  This package provides ways to print source code from the abstract
   --  syntax tree.

   procedure Sprint_Why_Node
     (Node : Why_Node_Id; To : Output_Id := Stdout) with
     Pre => (Get_Kind (Node) /= W_Unused_At_Start);
   --  Generate why code for Node and send it to Output_Id.

   procedure wpg (Node : Why_Node_Id);
   pragma Export (Ada, wpg);
   --  Print generated source for argument Node. Intended only for use
   --  from gdb for debugging purposes.

private
   type Printer_State is new Traversal_State with null record;

   procedure Base_Type_Pre_Op
     (State : in out Printer_State;
      Node  : W_Base_Type_Valid_Id);

   procedure Generic_Formal_Type_Pre_Op
     (State : in out Printer_State;
      Node  : W_Generic_Formal_Type_Valid_Id);

   procedure Generic_Actual_Type_Chain_Pre_Op
     (State : in out Printer_State;
      Node  : W_Generic_Actual_Type_Chain_Valid_Id);

   procedure Array_Type_Pre_Op
     (State : in out Printer_State;
      Node  : W_Array_Type_Valid_Id);

   procedure Array_Type_Post_Op
     (State : in out Printer_State;
      Node  : W_Array_Type_Valid_Id);

   procedure Ref_Type_Pre_Op
     (State : in out Printer_State;
      Node  : W_Ref_Type_Valid_Id);

   procedure Ref_Type_Post_Op
     (State : in out Printer_State;
      Node  : W_Ref_Type_Valid_Id);

   procedure Computation_Type_Pre_Op
     (State : in out Printer_State;
      Node  : W_Computation_Type_Valid_Id);

   procedure Effects_Pre_Op
     (State : in out Printer_State;
      Node  : W_Effects_Valid_Id);

   procedure Binder_Pre_Op
     (State : in out Printer_State;
      Node  : W_Binder_Valid_Id);

   procedure Constr_Decl_Pre_Op
     (State : in out Printer_State;
      Node  : W_Constr_Decl_Valid_Id);

   procedure Triggers_Pre_Op
     (State : in out Printer_State;
      Node  : W_Triggers_Valid_Id);

   procedure Trigger_Pre_Op
     (State : in out Printer_State;
      Node  : W_Trigger_Valid_Id);

   procedure Pattern_Pre_Op
     (State : in out Printer_State;
      Node  : W_Pattern_Valid_Id);

   procedure Match_Case_Pre_Op
     (State : in out Printer_State;
      Node  : W_Match_Case_Valid_Id);

   procedure Postcondition_Pre_Op
     (State : in out Printer_State;
      Node  : W_Postcondition_Valid_Id);

   procedure Exn_Condition_Pre_Op
     (State : in out Printer_State;
      Node  : W_Exn_Condition_Valid_Id);

   procedure Loop_Annot_Pre_Op
     (State : in out Printer_State;
      Node  : W_Loop_Annot_Valid_Id);

   procedure Wf_Arg_Pre_Op
     (State : in out Printer_State;
      Node  : W_Wf_Arg_Valid_Id);

   procedure Handler_Pre_Op
     (State : in out Printer_State;
      Node  : W_Handler_Valid_Id);

   procedure Universal_Quantif_Pre_Op
     (State : in out Printer_State;
      Node  : W_Universal_Quantif_Valid_Id);

   procedure Located_Predicate_Pre_Op
     (State : in out Printer_State;
      Node  : W_Located_Predicate_Valid_Id);

   procedure Existential_Quantif_Pre_Op
     (State : in out Printer_State;
      Node  : W_Existential_Quantif_Valid_Id);

   procedure Not_Pre_Op
     (State : in out Printer_State;
      Node  : W_Not_Valid_Id);

   procedure Relation_Pre_Op
     (State : in out Printer_State;
      Node  : W_Relation_Valid_Id);

   procedure Connection_Pre_Op
     (State : in out Printer_State;
      Node  : W_Connection_Valid_Id);

   procedure Identifier_Pre_Op
     (State : in out Printer_State;
      Node  : W_Identifier_Valid_Id);

   procedure Call_Pre_Op
     (State : in out Printer_State;
      Node  : W_Call_Valid_Id);

   procedure Literal_Pre_Op
     (State : in out Printer_State;
      Node  : W_Literal_Valid_Id);

   procedure Conditional_Pre_Op
     (State : in out Printer_State;
      Node  : W_Conditional_Valid_Id);

   procedure Integer_Constant_Pre_Op
     (State : in out Printer_State;
      Node  : W_Integer_Constant_Valid_Id);

   procedure Real_Constant_Pre_Op
     (State : in out Printer_State;
      Node  : W_Real_Constant_Valid_Id);

   procedure Void_Pre_Op
     (State : in out Printer_State;
      Node  : W_Void_Valid_Id);

   procedure Binary_Op_Pre_Op
     (State : in out Printer_State;
      Node  : W_Binary_Op_Valid_Id);

   procedure Unary_Op_Pre_Op
     (State : in out Printer_State;
      Node  : W_Unary_Op_Valid_Id);

   procedure Match_Pre_Op
     (State : in out Printer_State;
      Node  : W_Match_Valid_Id);

   procedure Binding_Pre_Op
     (State : in out Printer_State;
      Node  : W_Binding_Valid_Id);

   procedure Array_Access_Pre_Op
     (State : in out Printer_State;
      Node  : W_Array_Access_Valid_Id);

   procedure Any_Expr_Pre_Op
     (State : in out Printer_State;
      Node  : W_Any_Expr_Valid_Id);

   procedure Assignment_Pre_Op
     (State : in out Printer_State;
      Node  : W_Assignment_Valid_Id);

   procedure Array_Update_Pre_Op
     (State : in out Printer_State;
      Node  : W_Array_Update_Valid_Id);

   procedure Binding_Ref_Pre_Op
     (State : in out Printer_State;
      Node  : W_Binding_Ref_Valid_Id);

   procedure While_Loop_Pre_Op
     (State : in out Printer_State;
      Node  : W_While_Loop_Valid_Id);

   procedure Statement_Sequence_Pre_Op
     (State : in out Printer_State;
      Node  : W_Statement_Sequence_Valid_Id);

   procedure Label_Pre_Op
     (State : in out Printer_State;
      Node  : W_Label_Valid_Id);

   procedure Assert_Pre_Op
     (State : in out Printer_State;
      Node  : W_Assert_Valid_Id);

   procedure Assert_Post_Op
     (State : in out Printer_State;
      Node  : W_Assert_Valid_Id);

   procedure Raise_Pre_Op
     (State : in out Printer_State;
      Node  : W_Raise_Valid_Id);

   procedure Try_Block_Pre_Op
     (State : in out Printer_State;
      Node  : W_Try_Block_Valid_Id);

   procedure Unreachable_Code_Pre_Op
     (State : in out Printer_State;
      Node  : W_Unreachable_Code_Valid_Id);

   procedure Function_Decl_Pre_Op
     (State : in out Printer_State;
      Node  : W_Function_Decl_Valid_Id);

   procedure Function_Def_Pre_Op
     (State : in out Printer_State;
      Node  : W_Function_Def_Valid_Id);

   procedure Axiom_Pre_Op
     (State : in out Printer_State;
      Node  : W_Axiom_Valid_Id);

   procedure Goal_Pre_Op
     (State : in out Printer_State;
      Node  : W_Goal_Valid_Id);

   procedure Type_Pre_Op
     (State : in out Printer_State;
      Node  : W_Type_Valid_Id);

   procedure Global_Ref_Declaration_Pre_Op
     (State : in out Printer_State;
      Node  : W_Global_Ref_Declaration_Valid_Id);

   procedure Exception_Declaration_Pre_Op
     (State : in out Printer_State;
      Node  : W_Exception_Declaration_Valid_Id);

   procedure Include_Declaration_Pre_Op
     (State : in out Printer_State;
      Node  : W_Include_Declaration_Valid_Id);

   procedure File_Pre_Op
     (State : in out Printer_State;
      Node  : W_File_Valid_Id);

end Why.Atree.Sprint;
