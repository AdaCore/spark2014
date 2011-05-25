------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          X T R E E _ S I N F O                           --
--                                                                          --
--                                 B o d y                                  --
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

with Xtree_Tables; use Xtree_Tables;
with Xkind_Tables; use Xkind_Tables;

package body Xtree_Sinfo is

   procedure Build_AST is
   begin
      Register_Kinds;

      --  Classes

      New_Class ("W_Term",
                 W_Integer_Constant,
                 W_Protected_Term);
      New_Class ("W_Constant",
                 W_Integer_Constant,
                 W_Void_Literal);
      New_Class ("W_Arith_Op",
                 W_Op_Add,
                 W_Op_Modulo);
      New_Class ("W_Predicate",
                 W_True_Literal_Pred,
                 W_Protected_Predicate);
      New_Class ("W_Primitive_Type",
                 W_Type_Int,
                 W_Generic_Actual_Type_Chain);
      New_Class ("W_Relation",
                 W_Rel_Eq,
                 W_Rel_Ge);
      New_Class ("W_Logic_Declaration_Class",
                 W_Type,
                 W_Goal);
      New_Class ("W_Logic_Return_Type",
                 W_Type_Prop,
                 W_Generic_Actual_Type_Chain);
      New_Class ("W_Logic_Arg_Type",
                 W_Type_Int,
                 W_Array_Type);
      New_Class ("W_Simple_Value_Type",
                 W_Type_Int,
                 W_Ref_Type);
      New_Class ("W_Prog",
                 W_Prog_Constant,
                 W_Protected_Prog);
      New_Class ("W_Infix",
                 W_Op_Add_Prog,
                 W_Op_And_Then_Prog);
      New_Class ("W_Prefix",
                 W_Op_Minus_Prog,
                 W_Op_Not_Prog);
      New_Class ("W_Declaration",
                 W_Global_Binding,
                 W_Include_Declaration);
      New_Class ("W_Any_Node",
                 W_Identifier,
                 W_Include_Declaration);
      New_Class ("W_Type_Definition",
                 W_Transparent_Type_Definition,
                 W_Adt_Definition);

      --  AST

      Register_Special_Fields;
      New_Common_Field ("Ada_Node", "Node_Id");

      ------------------
      -- W_Identifier --
      ------------------

      New_Field (W_Identifier,
                 "Symbol", "Name_Id");
      New_Field (W_Identifier,
                 "Entity", "Why_Node_Id");

      ---------------------
      -- W_Abstract_Type --
      ---------------------

      New_Field (W_Abstract_Type,
                 "Name", "W_Identifier", Id_One);

      ---------------------------
      -- W_Generic_Formal_Type --
      ---------------------------

      New_Field (W_Generic_Formal_Type,
                 "Name", "W_Identifier", Id_One);

      ---------------------------------
      -- W_Generic_Actual_Type_Chain --
      ---------------------------------

      New_Field (W_Generic_Actual_Type_Chain,
                 "Type_Chain", "W_Primitive_Type", Id_Some);
      New_Field (W_Generic_Actual_Type_Chain,
                 "Name", "W_Identifier", Id_One);

      ------------------
      -- W_Array_Type --
      ------------------

      New_Field (W_Array_Type,
                 "Component_Type", "W_Primitive_Type", Id_One);

      ----------------
      -- W_Ref_Type --
      ----------------

      New_Field (W_Ref_Type,
                 "Aliased_Type", "W_Primitive_Type", Id_One);

      ------------------------
      -- W_Computation_Type --
      ------------------------

      New_Field (W_Computation_Type,
                 "Binders", "W_Binder", Id_Set);
      New_Field (W_Computation_Type,
                 "Precondition", "W_Predicate", Id_Lone);
      New_Field (W_Computation_Type,
                 "Result_Name", "W_Identifier", Id_Lone);
      New_Field (W_Computation_Type,
                 "Return_Type", "W_Primitive_Type", Id_One);
      New_Field (W_Computation_Type,
                 "Effects", "W_Effects", Id_One);
      New_Field (W_Computation_Type,
                 "Postcondition", "W_Postcondition", Id_Lone);

      ------------------------
      -- W_Integer_Constant --
      ------------------------

      New_Field (W_Integer_Constant,
                 "Value", "Uint");

      ---------------------
      -- W_Real_Constant --
      ---------------------

      New_Field (W_Real_Constant,
                 "Value", "Ureal");

      -----------------------
      -- W_Arith_Operation --
      -----------------------

      New_Field (W_Arith_Operation,
                 "Left", "W_Term", Id_One);
      New_Field (W_Arith_Operation,
                 "Op", "W_Arith_Op", Id_One);
      New_Field (W_Arith_Operation,
                 "Right", "W_Term", Id_One);

      ---------------------
      -- W_Negative_Term --
      ---------------------

      New_Field (W_Negative_Term,
                 "Operand", "W_Term", Id_One);

      -----------------------
      -- W_Term_Identifier --
      -----------------------

      New_Field (W_Term_Identifier,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Term_Identifier,
                 "Label", "W_Identifier", Id_Lone);

      -----------------
      -- W_Operation --
      -----------------

      New_Field (W_Operation,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Operation,
                 "Parameters", "W_Term", Id_Some);

      ------------------
      -- W_Named_Term --
      ------------------

      New_Field (W_Named_Term,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Named_Term,
                 "Term", "W_Term", Id_One);

      ------------------------
      -- W_Conditional_Term --
      ------------------------

      New_Field (W_Conditional_Term,
                 "Condition", "W_Term", Id_One);
      New_Field (W_Conditional_Term,
                 "Then_Part", "W_Term", Id_One);
      New_Field (W_Conditional_Term,
                 "Else_Part", "W_Term", Id_One);

      ---------------------
      -- W_Matching_Term --
      ---------------------

      New_Field (W_Matching_Term,
                 "Term", "W_Term", Id_One);
      New_Field (W_Matching_Term,
                 "Branches", "W_Match_Case", Id_Some);

      --------------------
      -- W_Binding_Term --
      --------------------

      New_Field (W_Binding_Term,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Binding_Term,
                 "Def", "W_Term", Id_One);
      New_Field (W_Binding_Term,
                 "Context", "W_Term", Id_One);

      ----------------------
      -- W_Protected_Term --
      ----------------------

      New_Field (W_Protected_Term,
                 "Term", "W_Term", Id_One);

      ----------------------------
      -- W_Predicate_Identifier --
      ----------------------------

      New_Field (W_Predicate_Identifier,
                 "Name", "W_Identifier", Id_One);

      --------------------------
      -- W_Predicate_Instance --
      --------------------------

      New_Field (W_Predicate_Instance,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Predicate_Instance,
                 "Parameters", "W_Term", Id_Some);

      ---------------------
      -- W_Related_Terms --
      ---------------------

      New_Field (W_Related_Terms,
                 "Left", "W_Term", Id_One);
      New_Field (W_Related_Terms,
                 "Op", "W_Relation", Id_One);
      New_Field (W_Related_Terms,
                 "Right", "W_Term", Id_One);
      New_Field (W_Related_Terms,
                 "Op2", "W_Relation", Id_Lone);
      New_Field (W_Related_Terms,
                 "Right2", "W_Term", Id_Lone);

      -------------------
      -- W_Implication --
      -------------------

      New_Field (W_Implication,
                 "Left", "W_Predicate", Id_One);
      New_Field (W_Implication,
                 "Right", "W_Predicate", Id_One);

      -------------------
      -- W_Equivalence --
      -------------------

      New_Field (W_Equivalence,
                 "Left", "W_Predicate", Id_One);
      New_Field (W_Equivalence,
                 "Right", "W_Predicate", Id_One);

      -------------------
      -- W_Disjunction --
      -------------------

      New_Field (W_Disjunction,
                 "Left", "W_Predicate", Id_One);
      New_Field (W_Disjunction,
                 "Right", "W_Predicate", Id_One);

      -------------------
      -- W_Conjunction --
      -------------------

      New_Field (W_Conjunction,
                 "Left", "W_Predicate", Id_One);
      New_Field (W_Conjunction,
                 "Right", "W_Predicate", Id_One);

      ----------------
      -- W_Negation --
      ----------------

      New_Field (W_Negation,
                 "Operand", "W_Predicate", Id_One);

      ------------------------
      -- W_Conditional_Pred --
      ------------------------

      New_Field (W_Conditional_Pred,
                 "Condition", "W_Term", Id_One);
      New_Field (W_Conditional_Pred,
                 "Then_Part", "W_Predicate", Id_One);
      New_Field (W_Conditional_Pred,
                 "Else_Part", "W_Predicate", Id_One);

      --------------------
      -- W_Binding_Pred --
      --------------------

      New_Field (W_Binding_Pred,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Binding_Pred,
                 "Def", "W_Term", Id_One);
      New_Field (W_Binding_Pred,
                 "Context", "W_Predicate", Id_One);

      -------------------------
      -- W_Universal_Quantif --
      -------------------------

      New_Field (W_Universal_Quantif,
                 "Variables", "W_Identifier", Id_Some);
      New_Field (W_Universal_Quantif,
                 "Var_Type", "W_Primitive_Type", Id_One);
      New_Field (W_Universal_Quantif,
                 "Triggers", "W_Triggers", Id_Lone);
      New_Field (W_Universal_Quantif,
                 "Pred", "W_Predicate", Id_One);

      ---------------------------
      -- W_Existential_Quantif --
      ---------------------------

      New_Field (W_Existential_Quantif,
                 "Variables", "W_Identifier", Id_Some);
      New_Field (W_Existential_Quantif,
                 "Var_Type", "W_Primitive_Type", Id_One);
      New_Field (W_Existential_Quantif,
                 "Pred", "W_Predicate", Id_One);

      -----------------------
      -- W_Named_Predicate --
      -----------------------

      New_Field (W_Named_Predicate,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Named_Predicate,
                 "Pred", "W_Predicate", Id_One);

      ---------------------------
      -- W_Protected_Predicate --
      ---------------------------

      New_Field (W_Protected_Predicate,
                 "Pred", "W_Predicate", Id_One);

      ---------------
      -- W_Pattern --
      ---------------

      New_Field (W_Pattern,
                 "Constr", "W_Identifier", Id_One);
      New_Field (W_Pattern,
                 "Args", "W_Identifier", Id_Set);

      ------------------
      -- W_Match_Case --
      ------------------

      New_Field (W_Match_Case,
                 "Pattern", "W_Pattern", Id_One);
      New_Field (W_Match_Case,
                 "Term", "W_Term", Id_One);

      ----------------
      -- W_Triggers --
      ----------------

      New_Field (W_Triggers,
                 "Triggers", "W_Trigger", Id_Some);

      ---------------
      -- W_Trigger --
      ---------------

      New_Field (W_Trigger,
                 "Terms", "W_Term", Id_Some);

      ------------
      -- W_Type --
      ------------

      New_Field (W_Type,
                 "External", "W_External", Id_Lone);
      New_Field (W_Type,
                 "Type_Parameters", "W_Identifier", Id_Set);
      New_Field (W_Type,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Type,
                 "Definition", "W_Type_Definition", Id_Lone);

      -------------
      -- W_Logic --
      -------------

      New_Field (W_Logic,
                 "External", "W_External", Id_Lone);
      New_Field (W_Logic,
                 "Names", "W_Identifier", Id_Some);
      New_Field (W_Logic,
                 "Logic_Type", "W_Logic_Type", Id_One);

      ----------------
      -- W_Function --
      ----------------

      New_Field (W_Function,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Function,
                 "Binders", "W_Logic_Binder", Id_Some);
      New_Field (W_Function,
                 "Return_Type", "W_Primitive_Type", Id_One);
      New_Field (W_Function,
                 "Def", "W_Term", Id_One);

      ----------------------------
      -- W_Predicate_Definition --
      ----------------------------

      New_Field (W_Predicate_Definition,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Predicate_Definition,
                 "Binders", "W_Logic_Binder", Id_Some);
      New_Field (W_Predicate_Definition,
                 "Def", "W_Predicate", Id_One);

      -----------------
      -- W_Inductive --
      -----------------

      New_Field (W_Inductive,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Inductive,
                 "Logic_Type", "W_Logic_Type", Id_One);
      New_Field (W_Inductive,
                 "Def", "W_Inductive_Case", Id_Some);

      -------------
      -- W_Axiom --
      -------------

      New_Field (W_Axiom,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Axiom,
                 "Def", "W_Predicate", Id_One);

      ------------
      -- W_Goal --
      ------------

      New_Field (W_Goal,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Goal,
                 "Def", "W_Predicate", Id_One);

      ------------------
      -- W_Logic_Type --
      ------------------

      New_Field (W_Logic_Type,
                 "Arg_Types", "W_Logic_Arg_Type", Id_Set);
      New_Field (W_Logic_Type,
                 "Return_Type", "W_Logic_Return_Type", Id_One);

      --------------------
      -- W_Logic_Binder --
      --------------------

      New_Field (W_Logic_Binder,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Logic_Binder,
                 "Param_Type", "W_Primitive_Type", Id_One);

      ----------------------
      -- W_Inductive_Case --
      ----------------------

      New_Field (W_Inductive_Case,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Inductive_Case,
                 "Pred", "W_Predicate", Id_One);

      -----------------------------------
      -- W_Transparent_Type_Definition --
      -----------------------------------

      New_Field (W_Transparent_Type_Definition,
                 "Type_Definition", "W_Primitive_Type", Id_One);

      ----------------------
      -- W_Adt_Definition --
      ----------------------

      New_Field (W_Adt_Definition,
                 "Constructors", "W_Constr_Decl", Id_Some);

      -------------------
      -- W_Constr_Decl --
      -------------------

      New_Field (W_Constr_Decl,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Constr_Decl,
                 "Arg_List", "W_Primitive_Type", Id_Set);

      ---------------
      -- W_Effects --
      ---------------

      New_Field (W_Effects,
                 "Reads", "W_Identifier", Id_Set);
      New_Field (W_Effects,
                 "Writes", "W_Identifier", Id_Set);
      New_Field (W_Effects,
                 "Raises", "W_Identifier", Id_Set);

      ---------------------
      -- W_Postcondition --
      ---------------------

      New_Field (W_Postcondition,
                 "Pred", "W_Predicate", Id_One);
      New_Field (W_Postcondition,
                 "Handlers", "W_Exn_Condition", Id_Set);

      ---------------------
      -- W_Exn_Condition --
      ---------------------

      New_Field (W_Exn_Condition,
                 "Exn_Case", "W_Identifier", Id_One);
      New_Field (W_Exn_Condition,
                 "Pred", "W_Predicate", Id_One);

      ---------------------
      -- W_Prog_Constant --
      ---------------------

      New_Field (W_Prog_Constant,
                 "Def", "W_Constant", Id_One);

      -----------------------
      -- W_Prog_Identifier --
      -----------------------

      New_Field (W_Prog_Identifier,
                 "Def", "W_Identifier", Id_One);

      ----------------
      -- W_Any_Expr --
      ----------------

      New_Field (W_Any_Expr,
                 "Any_Type", "W_Computation_Type", Id_One);

      -------------
      -- W_Deref --
      -------------

      New_Field (W_Deref,
                 "Ref", "W_Identifier", Id_One);

      ------------------
      -- W_Assignment --
      ------------------

      New_Field (W_Assignment,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Assignment,
                 "Value", "W_Prog", Id_One);

      --------------------
      -- W_Array_Access --
      --------------------

      New_Field (W_Array_Access,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Array_Access,
                 "Index", "W_Prog", Id_One);

      --------------------
      -- W_Array_Update --
      --------------------

      New_Field (W_Array_Update,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Array_Update,
                 "Index", "W_Prog", Id_One);
      New_Field (W_Array_Update,
                 "Value", "W_Prog", Id_One);

      ------------------
      -- W_Infix_Call --
      ------------------

      New_Field (W_Infix_Call,
                 "Left", "W_Prog", Id_One);
      New_Field (W_Infix_Call,
                 "Infix", "W_Infix", Id_One);
      New_Field (W_Infix_Call,
                 "Right", "W_Prog", Id_One);

      -------------------
      -- W_Prefix_Call --
      -------------------

      New_Field (W_Prefix_Call,
                 "Prefix", "W_Prefix", Id_One);
      New_Field (W_Prefix_Call,
                 "Operand", "W_Prog", Id_One);

      --------------------
      -- W_Binding_Prog --
      --------------------

      New_Field (W_Binding_Prog,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Binding_Prog,
                 "Def", "W_Prog", Id_One);
      New_Field (W_Binding_Prog,
                 "Context", "W_Prog", Id_One);

      -------------------
      -- W_Binding_Ref --
      -------------------

      New_Field (W_Binding_Ref,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Binding_Ref,
                 "Def", "W_Prog", Id_One);
      New_Field (W_Binding_Ref,
                 "Context", "W_Prog", Id_One);

      ------------------------
      -- W_Conditional_Prog --
      ------------------------

      New_Field (W_Conditional_Prog,
                 "Condition", "W_Prog", Id_One);
      New_Field (W_Conditional_Prog,
                 "Then_Part", "W_Prog", Id_One);
      New_Field (W_Conditional_Prog,
                 "Else_Part", "W_Prog", Id_Lone);

      ------------------
      -- W_While_Loop --
      ------------------

      New_Field (W_While_Loop,
                 "Condition", "W_Prog", Id_One);
      New_Field (W_While_Loop,
                 "Annotation", "W_Loop_Annot", Id_One);
      New_Field (W_While_Loop,
                 "Loop_Content", "W_Prog", Id_One);

      --------------------------
      -- W_Statement_Sequence --
      --------------------------

      New_Field (W_Statement_Sequence,
                 "Statements", "W_Prog", Id_Some);

      -------------
      -- W_Label --
      -------------

      New_Field (W_Label,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Label,
                 "Def", "W_Prog", Id_One);

      --------------
      -- W_Assert --
      --------------

      New_Field (W_Assert,
                 "Preds", "W_Predicate", Id_Some);
      New_Field (W_Assert,
                 "Prog", "W_Prog", Id_One);

      ----------------------
      -- W_Post_Assertion --
      ----------------------

      New_Field (W_Post_Assertion,
                 "Prog", "W_Prog", Id_One);
      New_Field (W_Post_Assertion,
                 "Post", "W_Postcondition", Id_One);

      ------------------------
      -- W_Opaque_Assertion --
      ------------------------

      New_Field (W_Opaque_Assertion,
                 "Prog", "W_Prog", Id_One);
      New_Field (W_Opaque_Assertion,
                 "Post", "W_Postcondition", Id_One);

      ---------------
      -- W_Fun_Def --
      ---------------

      New_Field (W_Fun_Def,
                 "Binders", "W_Binder", Id_Some);
      New_Field (W_Fun_Def,
                 "Pre", "W_Predicate", Id_One);
      New_Field (W_Fun_Def,
                 "Def", "W_Prog", Id_One);

      -------------------
      -- W_Binding_Fun --
      -------------------

      New_Field (W_Binding_Fun,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Binding_Fun,
                 "Binders", "W_Binder", Id_Some);
      New_Field (W_Binding_Fun,
                 "Pre", "W_Predicate", Id_One);
      New_Field (W_Binding_Fun,
                 "Def", "W_Prog", Id_One);
      New_Field (W_Binding_Fun,
                 "Context", "W_Prog", Id_One);

      -------------------
      -- W_Binding_Rec --
      -------------------

      New_Field (W_Binding_Rec,
                 "Recfun", "W_Recfun", Id_One);
      New_Field (W_Binding_Rec,
                 "Context", "W_Prog", Id_One);

      -----------------
      -- W_Prog_Call --
      -----------------

      New_Field (W_Prog_Call,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Prog_Call,
                 "Progs", "W_Prog", Id_Some);

      -----------------------
      -- W_Raise_Statement --
      -----------------------

      New_Field (W_Raise_Statement,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Raise_Statement,
                 "Exn_Type", "W_Simple_Value_Type", Id_Lone);

      ---------------------------------------
      -- W_Raise_Statement_With_Parameters --
      ---------------------------------------

      New_Field (W_Raise_Statement_With_Parameters,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Raise_Statement_With_Parameters,
                 "Parameter", "W_Term", Id_One);
      New_Field (W_Raise_Statement_With_Parameters,
                 "Exn_Type", "W_Simple_Value_Type", Id_Lone);

      -----------------
      -- W_Try_Block --
      -----------------

      New_Field (W_Try_Block,
                 "Prog", "W_Prog", Id_One);
      New_Field (W_Try_Block,
                 "Handler", "W_Handler", Id_Some);

      ------------------------
      -- W_Unreachable_Code --
      ------------------------

      New_Field (W_Unreachable_Code,
                 "Exn_Type", "W_Simple_Value_Type", Id_Lone);

      -------------------
      -- W_Begin_Block --
      -------------------

      New_Field (W_Begin_Block,
                 "Prog", "W_Prog", Id_One);

      ----------------------
      -- W_Protected_Prog --
      ----------------------

      New_Field (W_Protected_Prog,
                 "Prog", "W_Prog", Id_One);

      --------------
      -- W_Binder --
      --------------

      New_Field (W_Binder,
                 "Names", "W_Identifier", Id_Some);
      New_Field (W_Binder,
                 "Arg_Type", "W_Simple_Value_Type", Id_One);

      --------------
      -- W_Recfun --
      --------------

      New_Field (W_Recfun,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Recfun,
                 "Binders", "W_Binder", Id_Some);
      New_Field (W_Recfun,
                 "Return_Type", "W_Prog", Id_One);
      New_Field (W_Recfun,
                 "Variant", "W_Wf_Arg", Id_One);
      New_Field (W_Recfun,
                 "Pre", "W_Predicate", Id_One);
      New_Field (W_Recfun,
                 "Def", "W_Prog", Id_One);

      ------------------
      -- W_Loop_Annot --
      ------------------

      New_Field (W_Loop_Annot,
                 "Invariant", "W_Predicate", Id_Lone);
      New_Field (W_Loop_Annot,
                 "Variant", "W_Wf_Arg", Id_Lone);

      --------------
      -- W_Wf_Arg --
      --------------

      New_Field (W_Wf_Arg,
                 "Def", "W_Term", Id_One);
      New_Field (W_Wf_Arg,
                 "For_Id", "W_Identifier", Id_Lone);

      ---------------
      -- W_Handler --
      ---------------

      New_Field (W_Handler,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Handler,
                 "Parameter", "W_Prog", Id_Lone);
      New_Field (W_Handler,
                 "Def", "W_Prog", Id_One);

      ------------
      -- W_File --
      ------------

      New_Field (W_File,
                 "Declarations", "W_Declaration", Id_Set);

      ----------------------
      -- W_Global_Binding --
      ----------------------

      New_Field (W_Global_Binding,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Global_Binding,
                 "Binders", "W_Binder", Id_Set);
      New_Field (W_Global_Binding,
                 "Pre", "W_Predicate", Id_One);
      New_Field (W_Global_Binding,
                 "Def", "W_Prog", Id_One);

      --------------------------
      -- W_Global_Rec_Binding --
      --------------------------

      New_Field (W_Global_Rec_Binding,
                 "Name", "W_Recfun", Id_One);

      -----------------------------
      -- W_Parameter_Declaration --
      -----------------------------

      New_Field (W_Parameter_Declaration,
                 "External", "W_External", Id_Lone);
      New_Field (W_Parameter_Declaration,
                 "Names", "W_Identifier", Id_Some);
      New_Field (W_Parameter_Declaration,
                 "Parameter_Type", "W_Computation_Type", Id_One);

      ------------------------------
      -- W_Global_Ref_Declaration --
      ------------------------------

      New_Field (W_Global_Ref_Declaration,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Global_Ref_Declaration,
                 "Parameter_Type", "W_Primitive_Type", Id_One);

      -----------------------------
      -- W_Exception_Declaration --
      -----------------------------

      New_Field (W_Exception_Declaration,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Exception_Declaration,
                 "Parameter", "W_Primitive_Type", Id_Lone);

      -------------------------
      -- W_Logic_Declaration --
      -------------------------

      New_Field (W_Logic_Declaration,
                 "Decl", "W_Logic_Declaration_Class", Id_One);

      ---------------------------
      -- W_Include_Declaration --
      ---------------------------

      New_Field (W_Include_Declaration,
                 "Name", "W_Identifier", Id_One);

   end Build_AST;

end Xtree_Sinfo;
