------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          X T R E E _ S I N F O                           --
--                                                                          --
--                                 B o d y                                  --
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

with Why.Sinfo;      use Why.Sinfo;
with Xtree_Tables;   use Xtree_Tables;
with Xkind_Tables;   use Xkind_Tables;
with Xtree_Builders; use Xtree_Builders;

package body Xtree_Sinfo is

   procedure Build_AST is
   begin
      Register_Kinds;

      --  Domains

      New_Domain ("W_Expr",
                  "W_Expr",
                  W_Universal_Quantif,
                  W_Unreachable_Code);
      New_Domain ("W_Pred",
                  "W_Expr",
                  W_Universal_Quantif,
                  W_Conditional);
      New_Domain ("W_Term",
                  "W_Prog",
                  W_Identifier,
                  W_Record_Aggregate);
      New_Domain ("W_Prog",
                  "W_Expr",
                  W_Not,
                  W_Unreachable_Code);
      Init_Domains;

      --  Classes

      New_Class ("W_Value",
                 W_Not,
                 W_Unreachable_Code);
      New_Class ("W_Primitive_Type",
                 W_Base_Type,
                 W_Generic_Actual_Type_Chain);
      New_Class ("W_Simple_Value_Type",
                 W_Base_Type,
                 W_Ref_Type);

      New_Class ("W_Type_Definition",
                 W_Transparent_Type_Definition,
                 W_Record_Definition);
      New_Class ("W_Declaration",
                 W_Function_Decl,
                 W_Clone_Declaration);
      New_Class ("W_Any_Node",
                 W_Base_Type,
                 W_File);
      New_Class ("W_Generic_Theory",
                 W_Theory_Declaration,
                 W_Custom_Declaration);

      --  AST

      New_Common_Field ("Ada_Node", "Node_Id", "Empty");
      New_Domain_Field ("Domain", "EW_Domain", "EW_Prog");
      New_Special_Field ("Link", "Why_Node_Set", "Why_Empty");
      New_Special_Field ("Checked", "Boolean", Checked_Default_Value);

      -----------------
      -- W_Base_Type --
      -----------------

      --  Important note: when Base_Type = EW_Abstract, the Ada node must be
      --  specified.

      New_Field (W_Base_Type,
                 "Base_Type", "EW_Type");
      Set_Domain (W_Base_Type, EW_Term);

      ---------------------
      -- W_Abstract_Type --
      ---------------------

      --  Deprecated - use W_Base_Type with Base_Type = EW_Abstract instead

      New_Field (W_Abstract_Type,
                 "Name", "W_Identifier", Id_One);
      Set_Domain (W_Abstract_Type, EW_Term);

      ---------------------------
      -- W_Generic_Formal_Type --
      ---------------------------

      New_Field (W_Generic_Formal_Type,
                 "Name", "W_Identifier", Id_One);
      Set_Domain (W_Generic_Formal_Type, EW_Term);

      ---------------------------------
      -- W_Generic_Actual_Type_Chain --
      ---------------------------------

      New_Field (W_Generic_Actual_Type_Chain,
                 "Type_Chain", "W_Primitive_Type", Id_Some);
      New_Field (W_Generic_Actual_Type_Chain,
                 "Name", "W_Identifier", Id_One);
      Set_Domain (W_Generic_Actual_Type_Chain, EW_Term);

      ------------------
      -- W_Array_Type --
      ------------------

      New_Field (W_Array_Type,
                 "Component_Type", "W_Primitive_Type", Id_One);
      Set_Domain (W_Array_Type, EW_Prog);

      ----------------
      -- W_Ref_Type --
      ----------------

      New_Field (W_Ref_Type,
                 "Aliased_Type", "W_Primitive_Type", Id_One);
      Set_Domain (W_Ref_Type, EW_Prog);

      ------------------------
      -- W_Computation_Type --
      ------------------------

      New_Field (W_Computation_Type,
                 "Binders", "W_Binder", Id_Set);
      New_Field (W_Computation_Type,
                 "Result", "W_Binder", Id_One);
      New_Field (W_Computation_Type,
                 "Effects", "W_Effects", Id_Lone);
      New_Field (W_Computation_Type,
                 "Pre", "W_Pred", Id_Lone);
      New_Field (W_Computation_Type,
                 "Post", "W_Pred", Id_Lone);

      ---------------
      -- W_Effects --
      ---------------

      Set_Mutable (W_Effects);
      New_Field (W_Effects,
                 "Reads", "W_Identifier", Id_Set);
      New_Field (W_Effects,
                 "Writes", "W_Identifier", Id_Set);
      New_Field (W_Effects,
                 "Raises", "W_Identifier", Id_Set);
      Set_Domain (W_Effects, EW_Prog);

      --------------
      -- W_Binder --
      --------------

      New_Field (W_Binder,
                 "Name", "W_Identifier", Id_Lone);
      New_Field (W_Binder,
                 "Arg_Type", "W_Simple_Value_Type", Id_One);

      -----------------------------------
      -- W_Transparent_Type_Definition --
      -----------------------------------

      New_Field (W_Transparent_Type_Definition,
                 "Type_Definition", "W_Primitive_Type", Id_One);
      Set_Domain (W_Effects, EW_Term);

      ----------------------
      -- W_Adt_Definition --
      ----------------------

      New_Field (W_Adt_Definition,
                 "Constructors", "W_Constr_Decl", Id_Some);
      Set_Domain (W_Adt_Definition, EW_Term);

      -------------------
      -- W_Constr_Decl --
      -------------------

      New_Field (W_Constr_Decl,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Constr_Decl,
                 "Arg_List", "W_Primitive_Type", Id_Set);
      Set_Domain (W_Constr_Decl, EW_Term);

      -------------------------
      -- W_Record_Definition --
      -------------------------

      New_Field (W_Record_Definition,
                 "Fields", "W_Binder", Id_Some);
      Set_Domain (W_Record_Definition, EW_Term);

      ----------------
      -- W_Triggers --
      ----------------

      New_Field (W_Triggers,
                 "Triggers", "W_Trigger", Id_Some);
      Set_Domain (W_Triggers, EW_Term);

      ---------------
      -- W_Trigger --
      ---------------

      New_Field (W_Trigger,
                 "Terms", "W_Expr", Id_Some);
      Set_Domain (W_Trigger, EW_Term);

      ------------------
      -- W_Match_Case --
      ------------------

      New_Field (W_Match_Case,
                 "Pattern", "W_Term", Id_One);
      New_Field (W_Match_Case,
                 "Term", "W_Term", Id_One);
      Set_Domain (W_Match_Case, EW_Term);

      --------------
      -- W_Constr --
      --------------

      New_Field (W_Constr,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Constr,
                 "Args", "W_Expr", Id_Set);
      Set_Domain (W_Constr, EW_Term);

      ---------------------
      -- W_Postcondition --
      ---------------------

      New_Field (W_Postcondition,
                 "Pred", "W_Pred", Id_One);
      New_Field (W_Postcondition,
                 "Handlers", "W_Exn_Condition", Id_Set);
      Set_Domain (W_Postcondition, EW_Pred);

      ---------------------
      -- W_Exn_Condition --
      ---------------------

      New_Field (W_Exn_Condition,
                 "Exn_Case", "W_Identifier", Id_One);
      New_Field (W_Exn_Condition,
                 "Pred", "W_Pred", Id_One);
      Set_Domain (W_Exn_Condition, EW_Pred);

      ------------------
      -- W_Loop_Annot --
      ------------------

      New_Field (W_Loop_Annot,
                 "Invariant", "W_Pred", Id_Lone);
      New_Field (W_Loop_Annot,
                 "Variant", "W_Wf_Arg", Id_Lone);
      Set_Domain (W_Loop_Annot, EW_Prog);

      --------------
      -- W_Wf_Arg --
      --------------

      New_Field (W_Wf_Arg,
                 "Def", "W_Term", Id_One);
      New_Field (W_Wf_Arg,
                 "For_Id", "W_Identifier", Id_Lone);
      Set_Domain (W_Wf_Arg, EW_Term);

      ---------------
      -- W_Handler --
      ---------------

      New_Field (W_Handler,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Handler,
                 "Arg", "W_Prog", Id_Lone);
      New_Field (W_Handler,
                 "Def", "W_Prog", Id_One);
      Set_Domain (W_Handler, EW_Prog);

      -------------------------
      -- W_Field_Association --
      -------------------------

      New_Field (W_Field_Association,
                 "Field", "W_Identifier", Id_One);
      New_Field (W_Field_Association,
                 "Value", "W_Expr", Id_One);
      Set_Domain (W_Handler, EW_Term);

      -------------------------
      -- W_Universal_Quantif --
      -------------------------

      New_Field (W_Universal_Quantif,
                 "Variables", "W_Identifier", Id_Some);
      New_Field (W_Universal_Quantif,
                 "Labels", "W_Identifier", Id_Set);
      New_Field (W_Universal_Quantif,
                 "Var_Type", "W_Primitive_Type", Id_One);
      New_Field (W_Universal_Quantif,
                 "Triggers", "W_Triggers", Id_Lone);
      New_Field (W_Universal_Quantif,
                 "Pred", "W_Pred", Id_One);

      ---------------------------
      -- W_Existential_Quantif --
      ---------------------------

      New_Field (W_Existential_Quantif,
                 "Variables", "W_Identifier", Id_Some);
      New_Field (W_Existential_Quantif,
                 "Labels", "W_Identifier", Id_Set);
      New_Field (W_Existential_Quantif,
                 "Var_Type", "W_Primitive_Type", Id_One);
      New_Field (W_Existential_Quantif,
                 "Pred", "W_Pred", Id_One);

      -----------
      -- W_Not --
      -----------

      New_Field (W_Not,
                 "Right", "W_Expr", Id_One);

      ----------------
      -- W_Relation --
      ----------------

      New_Field (W_Relation,
                 "Op_Type", "EW_Not_Null_Type");
      New_Field (W_Relation,
                 "Left", "W_Value", Id_One);
      New_Field (W_Relation,
                 "Op", "EW_Relation");
      New_Field (W_Relation,
                 "Right", "W_Value", Id_One);
      New_Field (W_Relation,
                 "Op2", "EW_Relation", "EW_None");
      New_Field (W_Relation,
                 "Right2", "W_Value", Id_Lone);

      ------------------
      -- W_Connection --
      ------------------

      New_Field (W_Connection,
                 "Left", "W_Expr", Id_One);
      New_Field (W_Connection,
                 "Op", "EW_Connector");
      New_Field (W_Connection,
                 "Right", "W_Expr", Id_One);
      New_Field (W_Connection,
                 "More_Right", "W_Expr", Id_Set);

      -------------
      -- W_Label --
      -------------

      New_Field (W_Label,
                 "Labels", "W_Identifier", Id_Some);
      New_Field (W_Label,
                 "Def", "W_Expr", Id_One);

      ------------------
      -- W_Identifier --
      ------------------

      New_Field (W_Identifier, "Symbol", "Name_Id");
      New_Field (W_Identifier, "Context", "Name_Id");

      --------------
      -- W_Tagged --
      --------------

      New_Field (W_Tagged, "Tag", "Name_Id");
      New_Field (W_Tagged, "Def", "W_Expr", Id_One);

      ------------
      -- W_Call --
      ------------

      New_Field (W_Call,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Call,
                 "Args", "W_Expr", Id_Set);

      ---------------
      -- W_Literal --
      ---------------

      New_Field (W_Literal,
                 "Value", "EW_Literal");

      ---------------
      -- W_Binding --
      ---------------

      New_Field (W_Binding,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Binding,
                 "Def", "W_Value", Id_One);
      New_Field (W_Binding,
                 "Context", "W_Expr", Id_One);

      -------------
      -- W_Elsif --
      -------------

      New_Field (W_Elsif,
                 "Condition", "W_Expr", Id_One);
      New_Field (W_Elsif,
                 "Then_Part", "W_Expr", Id_One);

      -------------------
      -- W_Conditional --
      -------------------

      New_Field (W_Conditional,
                 "Condition", "W_Expr", Id_One);
      New_Field (W_Conditional,
                 "Then_Part", "W_Expr", Id_One);
      New_Field (W_Conditional,
                 "Elsif_Parts", "W_Expr", Id_Set);
      New_Field (W_Conditional,
                 "Else_Part", "W_Expr", Id_Lone);

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

      -----------------
      -- W_Binary_Op --
      -----------------

      New_Field (W_Binary_Op,
                 "Op", "EW_Binary_Op");
      New_Field (W_Binary_Op,
                 "Op_Type", "EW_Scalar");
      New_Field (W_Binary_Op,
                 "Left", "W_Expr", Id_One);
      New_Field (W_Binary_Op,
                 "Right", "W_Expr", Id_One);

      -----------------
      -- W_Unary_Op --
      -----------------

      New_Field (W_Unary_Op,
                 "Op", "EW_Unary_Op");
      New_Field (W_Unary_Op,
                 "Right", "W_Expr", Id_One);
      New_Field (W_Unary_Op,
                 "Op_Type", "EW_Scalar");

      -------------
      -- W_Deref --
      -------------

      New_Field (W_Deref,
                 "Right", "W_Identifier", Id_One);

      -------------
      -- W_Match --
      -------------

      Set_Mutable (W_Match);
      New_Field (W_Match,
                 "Term", "W_Term", Id_One);
      New_Field (W_Match,
                 "Branches", "W_Match_Case", Id_Some);

      --------------------
      -- W_Array_Access --
      --------------------

      New_Field (W_Array_Access,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Array_Access,
                 "Index", "W_Prog", Id_One);

      ---------------------
      -- W_Record_Access --
      ---------------------

      New_Field (W_Record_Access,
                 "Name", "W_Expr", Id_One);
      New_Field (W_Record_Access,
                 "Field", "W_Identifier", Id_One);

      ---------------------
      -- W_Record_Update --
      ---------------------

      New_Field (W_Record_Update,
                 "Name", "W_Expr", Id_One);
      New_Field (W_Record_Update,
                 "Updates", "W_Field_Association", Id_Some);

      ------------------------
      -- W_Record_Aggregate --
      ------------------------

      New_Field (W_Record_Aggregate,
                 "Associations", "W_Field_Association", Id_Some);

      ----------------
      -- W_Any_Expr --
      ----------------

      New_Field (W_Any_Expr,
                 "Any_Type", "W_Computation_Type", Id_One);

      ------------------
      -- W_Assignment --
      ------------------

      New_Field (W_Assignment,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Assignment,
                 "Value", "W_Prog", Id_One);

      --------------------
      -- W_Array_Update --
      --------------------

      New_Field (W_Array_Update,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Array_Update,
                 "Index", "W_Prog", Id_One);
      New_Field (W_Array_Update,
                 "Value", "W_Prog", Id_One);

      -------------------
      -- W_Binding_Ref --
      -------------------

      New_Field (W_Binding_Ref,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Binding_Ref,
                 "Def", "W_Prog", Id_One);
      New_Field (W_Binding_Ref,
                 "Labels", "W_Identifier", Id_Set);
      New_Field (W_Binding_Ref,
                 "Context", "W_Prog", Id_One);

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

      Set_Mutable (W_Statement_Sequence);
      New_Field (W_Statement_Sequence,
                 "Statements", "W_Prog", Id_Some);

      ---------------------
      -- W_Abstract_Expr --
      ---------------------

      Set_Domain (W_Abstract_Expr, EW_Prog);
      New_Field (W_Abstract_Expr,
                "Expr", "W_Prog", Id_One);
      New_Field (W_Abstract_Expr,
                "Post", "W_Pred", Id_One);

      --------------
      -- W_Assert --
      --------------

      New_Field (W_Assert,
                 "Pred", "W_Pred", Id_One);

      -------------
      -- W_Raise --
      -------------

      New_Field (W_Raise,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Raise,
                 "Exn_Type", "W_Simple_Value_Type", Id_Lone);

      -----------------
      -- W_Try_Block --
      -----------------

      New_Field (W_Try_Block,
                 "Prog", "W_Prog", Id_One);
      New_Field (W_Try_Block,
                 "Handler", "W_Handler", Id_Some);

      -----------------
      -- W_Tag_Intro --
      -----------------

      New_Field (W_Tag_Intro,
                 "Prog", "W_Prog", Id_One);
      New_Field (W_Tag_Intro, "Tag", "Name_Id");

      ------------------------
      -- W_Unreachable_Code --
      ------------------------

      New_Field (W_Unreachable_Code,
                 "Exn_Type", "W_Simple_Value_Type", Id_Lone);

      ---------------------
      -- W_Function_Decl --
      ---------------------

      New_Field (W_Function_Decl,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Function_Decl,
                 "Func_Type", "W_Computation_Type", Id_One);
      New_Field (W_Function_Decl,
                 "Labels", "W_Identifier", Id_Set);

      --------------------
      -- W_Function_Def --
      --------------------

      New_Field (W_Function_Def,
                 "Spec", "W_Function_Decl", Id_One);
      New_Field (W_Function_Def,
                 "Def", "W_Expr", Id_One);
      New_Field (W_Function_Def,
                 "Labels", "W_Identifier", Id_Set);

      -------------
      -- W_Axiom --
      -------------

      New_Field (W_Axiom,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Axiom,
                 "Def", "W_Pred", Id_One);
      Set_Domain (W_Axiom, EW_Term);

      ------------
      -- W_Goal --
      ------------

      New_Field (W_Goal,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Goal,
                 "Def", "W_Pred", Id_One);
      Set_Domain (W_Goal, EW_Term);

      ------------
      -- W_Type --
      ------------

      New_Field (W_Type,
                 "Args", "W_Identifier", Id_Set);
      New_Field (W_Type,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Type,
                 "Labels", "W_Identifier", Id_Set);
      New_Field (W_Type,
                 "Definition", "W_Type_Definition", Id_Lone);
      Set_Domain (W_Type, EW_Term);

      ------------------------------
      -- W_Global_Ref_Declaration --
      ------------------------------

      New_Field (W_Global_Ref_Declaration,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Global_Ref_Declaration,
                 "Ref_Type", "W_Primitive_Type", Id_One);
      New_Field (W_Global_Ref_Declaration,
                 "Labels", "W_Identifier", Id_Set);
      Set_Domain (W_Global_Ref_Declaration, EW_Prog);

      -----------------------------
      -- W_Exception_Declaration --
      -----------------------------

      New_Field (W_Exception_Declaration,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Exception_Declaration,
                 "Arg", "W_Primitive_Type", Id_Lone);
      Set_Domain (W_Exception_Declaration, EW_Prog);

      ---------------------------
      -- W_Include_Declaration --
      ---------------------------

      New_Field (W_Include_Declaration,
                 "File", "W_Identifier", Id_Lone);
      New_Field (W_Include_Declaration,
                 "T_Name", "W_Identifier", Id_One);
      New_Field (W_Include_Declaration,
                 "Kind", "EW_Theory_Type");
      New_Field (W_Include_Declaration,
                 "Use_Kind", "EW_Clone_Type");
      Set_Domain (W_Include_Declaration, EW_Term);

      -------------------------
      -- W_Clone_Declaration --
      -------------------------

      New_Field (W_Clone_Declaration,
                 "Origin", "W_Identifier", Id_One);
      New_Field (W_Clone_Declaration,
                 "As_Name", "W_Identifier", Id_Lone);
      New_Field (W_Clone_Declaration,
                 "Clone_Kind", "EW_Clone_Type");
      New_Field (W_Clone_Declaration,
                 "Substitutions", "W_Clone_Substitution", Id_Set);
      New_Field (W_Clone_Declaration,
                 "Theory_Kind", "EW_Theory_Type");
      Set_Domain (W_Clone_Declaration, EW_Term);

      --------------------------
      -- W_Clone_Substitution --
      --------------------------

      New_Field (W_Clone_Substitution, "Kind", "EW_Subst_Type");
      New_Field (W_Clone_Substitution,
                 "Orig_Name", "W_Identifier", Id_One);
      New_Field (W_Clone_Substitution,
                 "Image", "W_Identifier", Id_One);
      Set_Domain (W_Clone_Substitution, EW_Term);

      --------------------------
      -- W_Theory_Declaration --
      --------------------------

      Set_Mutable (W_Theory_Declaration);
      New_Field (W_Theory_Declaration,
                 "Declarations", "W_Declaration", Id_Set);
      New_Field (W_Theory_Declaration,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Theory_Declaration,
                 "Kind", "EW_Theory_Type");
      New_Field (W_Theory_Declaration,
                 "Includes", "W_Include_Declaration", Id_Set);
      New_Field (W_Theory_Declaration,
                 "Comment", "W_Identifier", Id_Lone);
      Set_Domain (W_Theory_Declaration, EW_Prog);

      ---------------------------
      -- W_Custom_Substitution --
      ---------------------------

      New_Field (W_Custom_Substitution,
                 "From", "Name_Id");

      New_Field (W_Custom_Substitution,
                 "To", "W_Any_Node", Id_One);

      --------------------------
      -- W_Custom_Declaration --
      --------------------------

      New_Field (W_Custom_Declaration,
                 "File_Name", "Name_Id");

      New_Field (W_Custom_Declaration,
                 "Subst", "W_Custom_Substitution", Id_Set);

      ------------
      -- W_File --
      ------------

      Set_Mutable (W_File);
      New_Field (W_File,
                 "Theories", "W_Generic_Theory", Id_Set);
      Set_Domain (W_File, EW_Prog);

   end Build_AST;

end Xtree_Sinfo;
