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
-- gnat2why is  free  software;  you can redistribute it and/or modify it   --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. gnat2why is distributed in the hope that it will  be  useful,   --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHAN-  --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
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

private
   type Printer_State is new Traversal_State with null record;

   procedure Identifier_Pre_Op
     (State : in out Printer_State;
      Node  : W_Identifier_Id);

   procedure Type_Prop_Pre_Op
     (State : in out Printer_State;
      Node  : W_Type_Prop_Id);

   procedure Type_Int_Pre_Op
     (State : in out Printer_State;
      Node  : W_Type_Int_Id);

   procedure Type_Bool_Pre_Op
     (State : in out Printer_State;
      Node  : W_Type_Bool_Id);

   procedure Type_Real_Pre_Op
     (State : in out Printer_State;
      Node  : W_Type_Real_Id);

   procedure Type_Unit_Pre_Op
     (State : in out Printer_State;
      Node  : W_Type_Unit_Id);

   procedure Generic_Formal_Type_Pre_Op
     (State : in out Printer_State;
      Node  : W_Generic_Formal_Type_Id);

   procedure Generic_Actual_Type_Chain_Pre_Op
     (State : in out Printer_State;
      Node  : W_Generic_Actual_Type_Chain_Id);

   procedure Array_Type_Post_Op
     (State : in out Printer_State;
      Node  : W_Array_Type_Id);

   procedure Ref_Type_Post_Op
     (State : in out Printer_State;
      Node  : W_Ref_Type_Id);

   procedure Protected_Value_Type_Pre_Op
     (State : in out Printer_State;
      Node  : W_Protected_Value_Type_Id);

   procedure Protected_Value_Type_Post_Op
     (State : in out Printer_State;
      Node  : W_Protected_Value_Type_Id);

   procedure Arrow_Type_Pre_Op
     (State : in out Printer_State;
      Node  : W_Arrow_Type_Id);

   procedure Precondition_Pre_Op
     (State : in out Printer_State;
      Node  : W_Precondition_Id);

   procedure Computation_Spec_Pre_Op
     (State : in out Printer_State;
      Node  : W_Computation_Spec_Id);

   procedure Integer_Constant_Pre_Op
     (State : in out Printer_State;
      Node  : W_Integer_Constant_Id);

   procedure Real_Constant_Pre_Op
     (State : in out Printer_State;
      Node  : W_Real_Constant_Id);

   procedure True_Literal_Pre_Op
     (State : in out Printer_State;
      Node  : W_True_Literal_Id);

   procedure False_Literal_Pre_Op
     (State : in out Printer_State;
      Node  : W_False_Literal_Id);

   procedure Void_Literal_Pre_Op
     (State : in out Printer_State;
      Node  : W_Void_Literal_Id);

   procedure Arith_Operation_Pre_Op
     (State : in out Printer_State;
      Node  : W_Arith_Operation_Id);

   procedure Negative_Term_Pre_Op
     (State : in out Printer_State;
      Node  : W_Negative_Term_Id);

   procedure Label_Identifier_Pre_Op
     (State : in out Printer_State;
      Node  : W_Label_Identifier_Id);

   procedure Operation_Pre_Op
     (State : in out Printer_State;
      Node  : W_Operation_Id);

   procedure Named_Term_Pre_Op
     (State : in out Printer_State;
      Node  : W_Named_Term_Id);

   procedure Matching_Term_Pre_Op
     (State : in out Printer_State;
      Node  : W_Matching_Term_Id);

   procedure Pattern_Pre_Op
     (State : in out Printer_State;
      Node  : W_Pattern_Id);

   procedure Match_Case_Pre_Op
     (State : in out Printer_State;
      Node  : W_Match_Case_Id);

   procedure Conditional_Term_Pre_Op
     (State : in out Printer_State;
      Node  : W_Conditional_Term_Id);

   procedure Binding_Term_Pre_Op
     (State : in out Printer_State;
      Node  : W_Binding_Term_Id);

   procedure Protected_Term_Pre_Op
     (State : in out Printer_State;
      Node  : W_Protected_Term_Id);

   procedure Protected_Term_Post_Op
     (State : in out Printer_State;
      Node  : W_Protected_Term_Id);

   procedure Op_Add_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Add_Id);

   procedure Op_Substract_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Substract_Id);

   procedure Op_Multiply_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Multiply_Id);

   procedure Op_Divide_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Divide_Id);

   procedure Op_Modulo_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Modulo_Id);

   procedure True_Literal_Pred_Pre_Op
     (State : in out Printer_State;
      Node  : W_True_Literal_Pred_Id);

   procedure False_Literal_Pred_Pre_Op
     (State : in out Printer_State;
      Node  : W_False_Literal_Pred_Id);

   procedure Predicate_Instance_Pre_Op
     (State : in out Printer_State;
      Node  : W_Predicate_Instance_Id);

   procedure Related_Terms_Pre_Op
     (State : in out Printer_State;
      Node  : W_Related_Terms_Id);

   procedure Implication_Pre_Op
     (State : in out Printer_State;
      Node  : W_Implication_Id);

   procedure Equivalence_Pre_Op
     (State : in out Printer_State;
      Node  : W_Equivalence_Id);

   procedure Disjonction_Pre_Op
     (State : in out Printer_State;
      Node  : W_Disjonction_Id);

   procedure Conjonction_Pre_Op
     (State : in out Printer_State;
      Node  : W_Conjonction_Id);

   procedure Negation_Pre_Op
     (State : in out Printer_State;
      Node  : W_Negation_Id);

   procedure Conditional_Pred_Pre_Op
     (State : in out Printer_State;
      Node  : W_Conditional_Pred_Id);

   procedure Binding_Pred_Pre_Op
     (State : in out Printer_State;
      Node  : W_Binding_Pred_Id);

   procedure Universal_Quantif_Pre_Op
     (State : in out Printer_State;
      Node  : W_Universal_Quantif_Id);

   procedure Existential_Quantif_Pre_Op
     (State : in out Printer_State;
      Node  : W_Existential_Quantif_Id);

   procedure Named_Predicate_Pre_Op
     (State : in out Printer_State;
      Node  : W_Named_Predicate_Id);

   procedure Protected_Predicate_Pre_Op
     (State : in out Printer_State;
      Node  : W_Protected_Predicate_Id);

   procedure Protected_Predicate_Post_Op
     (State : in out Printer_State;
      Node  : W_Protected_Predicate_Id);

   procedure Triggers_Pre_Op
     (State : in out Printer_State;
      Node  : W_Triggers_Id);

   procedure Trigger_Pre_Op
     (State : in out Printer_State;
      Node  : W_Trigger_Id);

   procedure Rel_Eq_Pre_Op
     (State : in out Printer_State;
      Node  : W_Rel_Eq_Id);

   procedure Rel_Ne_Pre_Op
     (State : in out Printer_State;
      Node  : W_Rel_Ne_Id);

   procedure Rel_Lt_Pre_Op
     (State : in out Printer_State;
      Node  : W_Rel_Lt_Id);

   procedure Rel_Le_Pre_Op
     (State : in out Printer_State;
      Node  : W_Rel_Le_Id);

   procedure Rel_Gt_Pre_Op
     (State : in out Printer_State;
      Node  : W_Rel_Gt_Id);

   procedure Rel_Ge_Pre_Op
     (State : in out Printer_State;
      Node  : W_Rel_Ge_Id);

   procedure Type_Pre_Op
     (State : in out Printer_State;
      Node  : W_Type_Id);

   procedure Constr_Decl_Pre_Op
      (State : in out Printer_State;
       Node : W_Constr_Decl_Id);

   procedure Logic_Pre_Op
     (State : in out Printer_State;
      Node  : W_Logic_Id);

   procedure Function_Pre_Op
     (State : in out Printer_State;
      Node  : W_Function_Id);

   procedure Predicate_Definition_Pre_Op
     (State : in out Printer_State;
      Node  : W_Predicate_Definition_Id);

   procedure Inductive_Pre_Op
     (State : in out Printer_State;
      Node  : W_Inductive_Id);

   procedure Axiom_Pre_Op
     (State : in out Printer_State;
      Node  : W_Axiom_Id);

   procedure Goal_Pre_Op
     (State : in out Printer_State;
      Node  : W_Goal_Id);

   procedure External_Pre_Op
     (State : in out Printer_State;
      Node  : W_External_Id);

   procedure Logic_Type_Pre_Op
     (State : in out Printer_State;
      Node  : W_Logic_Type_Id);

   procedure Logic_Binder_Pre_Op
     (State : in out Printer_State;
      Node  : W_Logic_Binder_Id);

   procedure Inductive_Case_Pre_Op
     (State : in out Printer_State;
      Node  : W_Inductive_Case_Id);

   procedure Effects_Pre_Op
     (State : in out Printer_State;
      Node  : W_Effects_Id);

   procedure Postcondition_Pre_Op
     (State : in out Printer_State;
      Node  : W_Postcondition_Id);

   procedure Exn_Condition_Pre_Op
     (State : in out Printer_State;
      Node  : W_Exn_Condition_Id);

   procedure Assertion_Pre_Op
     (State : in out Printer_State;
      Node  : W_Assertion_Id);

   procedure Deref_Pre_Op
     (State : in out Printer_State;
      Node  : W_Deref_Id);

   procedure Assignment_Pre_Op
     (State : in out Printer_State;
      Node  : W_Assignment_Id);

   procedure Array_Access_Pre_Op
     (State : in out Printer_State;
      Node  : W_Array_Access_Id);

   procedure Array_Update_Pre_Op
     (State : in out Printer_State;
      Node  : W_Array_Update_Id);

   procedure Infix_Call_Pre_Op
     (State : in out Printer_State;
      Node  : W_Infix_Call_Id);

   procedure Prefix_Call_Pre_Op
     (State : in out Printer_State;
      Node  : W_Prefix_Call_Id);

   procedure Binding_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Binding_Prog_Id);

   procedure Binding_Ref_Pre_Op
     (State : in out Printer_State;
      Node  : W_Binding_Ref_Id);

   procedure Conditional_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Conditional_Prog_Id);

   procedure While_Loop_Pre_Op
     (State : in out Printer_State;
      Node  : W_While_Loop_Id);

   procedure Statement_Sequence_Pre_Op
     (State : in out Printer_State;
      Node  : W_Statement_Sequence_Id);

   procedure Label_Pre_Op
     (State : in out Printer_State;
      Node  : W_Label_Id);

   procedure Assert_Pre_Op
     (State : in out Printer_State;
      Node  : W_Assert_Id);

   procedure Post_Assertion_Pre_Op
     (State : in out Printer_State;
      Node  : W_Post_Assertion_Id);

   procedure Opaque_Assertion_Pre_Op
     (State : in out Printer_State;
      Node  : W_Opaque_Assertion_Id);

   procedure Fun_Def_Pre_Op
     (State : in out Printer_State;
      Node  : W_Fun_Def_Id);

   procedure Binding_Fun_Pre_Op
     (State : in out Printer_State;
      Node  : W_Binding_Fun_Id);

   procedure Binding_Rec_Pre_Op
     (State : in out Printer_State;
      Node  : W_Binding_Rec_Id);

   procedure Prog_Sequence_Pre_Op
     (State : in out Printer_State;
      Node  : W_Prog_Sequence_Id);

   procedure Raise_Statement_Pre_Op
     (State : in out Printer_State;
      Node  : W_Raise_Statement_Id);

   procedure Raise_Statement_With_Parameters_Pre_Op
     (State : in out Printer_State;
      Node  : W_Raise_Statement_With_Parameters_Id);

   procedure Try_Block_Pre_Op
     (State : in out Printer_State;
      Node  : W_Try_Block_Id);

   procedure Unreachable_Code_Pre_Op
     (State : in out Printer_State;
      Node  : W_Unreachable_Code_Id);

   procedure Begin_Block_Pre_Op
     (State : in out Printer_State;
      Node  : W_Begin_Block_Id);

   procedure Begin_Block_Post_Op
     (State : in out Printer_State;
      Node  : W_Begin_Block_Id);

   procedure Protected_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Protected_Prog_Id);

   procedure Protected_Prog_Post_Op
     (State : in out Printer_State;
      Node  : W_Protected_Prog_Id);

   procedure Op_Add_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Add_Prog_Id);

   procedure Op_Substract_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Substract_Prog_Id);

   procedure Op_Multiply_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Multiply_Prog_Id);

   procedure Op_Divide_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Divide_Prog_Id);

   procedure Op_Mod_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Mod_Prog_Id);

   procedure Op_Eq_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Eq_Prog_Id);

   procedure Op_Ne_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Ne_Prog_Id);

   procedure Op_Lt_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Lt_Prog_Id);

   procedure Op_Le_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Le_Prog_Id);

   procedure Op_Gt_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Gt_Prog_Id);

   procedure Op_Ge_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Ge_Prog_Id);

   procedure Op_Or_Else_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Or_Else_Prog_Id);

   procedure Op_And_Then_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_And_Then_Prog_Id);

   procedure Op_Minus_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Minus_Prog_Id);

   procedure Op_Not_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Not_Prog_Id);

   procedure Binders_Pre_Op
     (State : in out Printer_State;
      Node  : W_Binders_Id);

   procedure Binder_Pre_Op
     (State : in out Printer_State;
      Node  : W_Binder_Id);

   procedure Recfun_Pre_Op
     (State : in out Printer_State;
      Node  : W_Recfun_Id);

   procedure Loop_Annot_Pre_Op
     (State : in out Printer_State;
      Node  : W_Loop_Annot_Id);

   procedure Wf_Arg_Pre_Op
     (State : in out Printer_State;
      Node  : W_Wf_Arg_Id);

   procedure Handler_Pre_Op
     (State : in out Printer_State;
      Node  : W_Handler_Id);

   procedure File_Pre_Op
     (State : in out Printer_State;
      Node  : W_File_Id);

   procedure Global_Binding_Pre_Op
     (State : in out Printer_State;
      Node  : W_Global_Binding_Id);

   procedure Global_Rec_Binding_Pre_Op
     (State : in out Printer_State;
      Node  : W_Global_Rec_Binding_Id);

   procedure Parameter_Declaration_Pre_Op
     (State : in out Printer_State;
      Node  : W_Parameter_Declaration_Id);

   procedure Exception_Declaration_Pre_Op
     (State : in out Printer_State;
      Node  : W_Exception_Declaration_Id);

end Why.Atree.Sprint;
