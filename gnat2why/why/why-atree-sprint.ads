------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                     W H Y - A T R E E - S P R I N T                      --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2013, AdaCore                   --
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

   procedure Type_Pre_Op
     (State : in out Printer_State;
      Node  : W_Type_Id);

   procedure Effects_Pre_Op
     (State : in out Printer_State;
      Node  : W_Effects_Id);

   procedure Binder_Pre_Op
     (State : in out Printer_State;
      Node  : W_Binder_Id);

   procedure Record_Definition_Pre_Op
      (State : in out Printer_State;
       Node : W_Record_Definition_Id);

   procedure Triggers_Pre_Op
     (State : in out Printer_State;
      Node  : W_Triggers_Id);

   procedure Trigger_Pre_Op
     (State : in out Printer_State;
      Node  : W_Trigger_Id);

   procedure Postcondition_Pre_Op
     (State : in out Printer_State;
      Node  : W_Postcondition_Id);

   procedure Exn_Condition_Pre_Op
     (State : in out Printer_State;
      Node  : W_Exn_Condition_Id);

   procedure Loop_Annot_Pre_Op
     (State : in out Printer_State;
      Node  : W_Loop_Annot_Id);

   procedure Wf_Arg_Pre_Op
     (State : in out Printer_State;
      Node  : W_Wf_Arg_Id);

   procedure Handler_Pre_Op
     (State : in out Printer_State;
      Node  : W_Handler_Id);

   procedure Universal_Quantif_Pre_Op
     (State : in out Printer_State;
      Node  : W_Universal_Quantif_Id);

   procedure Existential_Quantif_Pre_Op
     (State : in out Printer_State;
      Node  : W_Existential_Quantif_Id);

   procedure Not_Pre_Op
     (State : in out Printer_State;
      Node  : W_Not_Id);

   procedure Relation_Pre_Op
     (State : in out Printer_State;
      Node  : W_Relation_Id);

   procedure Connection_Pre_Op
     (State : in out Printer_State;
      Node  : W_Connection_Id);

   procedure Identifier_Pre_Op
     (State : in out Printer_State;
      Node  : W_Identifier_Id);

   procedure Tagged_Pre_Op
     (State : in out Printer_State;
      Node  : W_Tagged_Id);

   procedure Call_Pre_Op
     (State : in out Printer_State;
      Node  : W_Call_Id);

   procedure Literal_Pre_Op
     (State : in out Printer_State;
      Node  : W_Literal_Id);

   procedure Elsif_Pre_Op
     (State : in out Printer_State;
      Node  : W_Elsif_Id);

   procedure Conditional_Pre_Op
     (State : in out Printer_State;
      Node  : W_Conditional_Id);

   procedure Integer_Constant_Pre_Op
     (State : in out Printer_State;
      Node  : W_Integer_Constant_Id);

   procedure Real_Constant_Pre_Op
     (State : in out Printer_State;
      Node  : W_Real_Constant_Id);

   procedure Void_Pre_Op
     (State : in out Printer_State;
      Node  : W_Void_Id);

   procedure Binary_Op_Pre_Op
     (State : in out Printer_State;
      Node  : W_Binary_Op_Id);

   procedure Unary_Op_Pre_Op
     (State : in out Printer_State;
      Node  : W_Unary_Op_Id);

   procedure Deref_Pre_Op
     (State : in out Printer_State;
      Node  : W_Deref_Id);

   procedure Binding_Pre_Op
     (State : in out Printer_State;
      Node  : W_Binding_Id);

   procedure Record_Access_Pre_Op
     (State : in out Printer_State;
      Node  : W_Record_Access_Id);

   procedure Record_Update_Pre_Op
     (State : in out Printer_State;
      Node  : W_Record_Update_Id);

   procedure Record_Aggregate_Pre_Op
     (State : in out Printer_State;
      Node  : W_Record_Aggregate_Id);

   procedure Field_Association_Pre_Op
     (State : in out Printer_State;
      Node  : W_Field_Association_Id);

   procedure Any_Expr_Pre_Op
     (State : in out Printer_State;
      Node  : W_Any_Expr_Id);

   procedure Assignment_Pre_Op
     (State : in out Printer_State;
      Node  : W_Assignment_Id);

   procedure Binding_Ref_Pre_Op
     (State : in out Printer_State;
      Node  : W_Binding_Ref_Id);

   procedure While_Loop_Pre_Op
     (State : in out Printer_State;
      Node  : W_While_Loop_Id);

   procedure Statement_Sequence_Pre_Op
     (State : in out Printer_State;
      Node  : W_Statement_Sequence_Id);

   procedure Abstract_Expr_Pre_Op
     (State : in out Printer_State;
      Node  : W_Abstract_Expr_Id);

   procedure Label_Pre_Op
     (State : in out Printer_State;
      Node  : W_Label_Id);

   procedure Assert_Pre_Op
     (State : in out Printer_State;
      Node  : W_Assert_Id);

   procedure Assert_Post_Op
     (State : in out Printer_State;
      Node  : W_Assert_Id);

   procedure Raise_Pre_Op
     (State : in out Printer_State;
      Node  : W_Raise_Id);

   procedure Try_Block_Pre_Op
     (State : in out Printer_State;
      Node  : W_Try_Block_Id);

   procedure Function_Decl_Pre_Op
     (State : in out Printer_State;
      Node  : W_Function_Decl_Id);

   procedure Function_Def_Pre_Op
     (State : in out Printer_State;
      Node  : W_Function_Def_Id);

   procedure Axiom_Pre_Op
     (State : in out Printer_State;
      Node  : W_Axiom_Id);

   procedure Goal_Pre_Op
     (State : in out Printer_State;
      Node  : W_Goal_Id);

   procedure Type_Decl_Pre_Op
     (State : in out Printer_State;
      Node  : W_Type_Decl_Id);

   procedure Global_Ref_Declaration_Pre_Op
     (State : in out Printer_State;
      Node  : W_Global_Ref_Declaration_Id);

   procedure Exception_Declaration_Pre_Op
     (State : in out Printer_State;
      Node  : W_Exception_Declaration_Id);

   procedure Include_Declaration_Pre_Op
     (State : in out Printer_State;
      Node  : W_Include_Declaration_Id);

   procedure Clone_Declaration_Pre_Op
      (State : in out Printer_State;
       Node  : W_Clone_Declaration_Id);

   procedure Clone_Substitution_Pre_Op
      (State : in out Printer_State;
       Node  : W_Clone_Substitution_Id);

   procedure Theory_Declaration_Pre_Op
     (State : in out Printer_State;
      Node  : W_Theory_Declaration_Id);

   procedure Custom_Declaration_Pre_Op
     (State : in out Printer_State;
      Node  : W_Custom_Declaration_Id);

   procedure File_Pre_Op
     (State : in out Printer_State;
      Node  : W_File_Id);

end Why.Atree.Sprint;
