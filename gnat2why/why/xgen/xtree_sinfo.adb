------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          X T R E E _ S I N F O                           --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2020, AdaCore                     --
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

   --  See the Makefile for overall behavior information
   procedure Build_AST is
   begin
      Register_Kinds;

      --  Domains

      New_Domain ("W_Expr",
                  "W_Expr",
                  W_Universal_Quantif,
                  W_Try_Block);
      New_Domain ("W_Pred",
                  "W_Expr",
                  W_Universal_Quantif,
                  W_Conditional);
      New_Domain ("W_Term",
                  "W_Prog",
                  W_Label,
                  W_Record_Aggregate);
      New_Domain ("W_Prog",
                  "W_Expr",
                  W_Not,
                  W_Try_Block);
      Init_Domains;

      --  Classes

      New_Class ("W_Type_Definition",
                 W_Transparent_Type_Definition,
                 W_Range_Type_Definition);
      New_Class ("W_Declaration",
                 W_Function_Decl,
                 W_Clone_Declaration);
      New_Class ("W_Any_Node",
                 W_Type,
                 W_Module);
      New_Class ("W_Generic_Theory",
                 W_Theory_Declaration,
                 W_Custom_Declaration);

      --  AST

      New_Common_Field ("Ada_Node", "Node_Id", "Empty");
      New_Domain_Field ("Domain", "EW_Domain", "EW_Prog");
      New_Special_Field ("Link", "Why_Node_Set", "Why_Empty");
      New_Special_Field ("Checked", "Boolean", Checked_Default_Value);

      ------------
      -- W_Name --
      ------------

      New_Field (W_Name, "Symb", "Symbol");
      New_Field (W_Name, "Namespace", "Symbol", "No_Symbol");
      New_Field (W_Name, "Module", "W_Module", Id_Lone);
      New_Field (W_Name, "Infix", "Boolean", "False");
      Set_Domain (W_Name, EW_Term);

      ------------
      -- W_Type --
      ------------

      New_Field (W_Type,
                 "Type_Kind", "EW_Type");
      New_Field (W_Type,
                 "Name", "W_Name", Id_One);
      New_Field (W_Type,
                 "Is_Mutable", "Boolean", "False");
      Set_Domain (W_Type, EW_Term);

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
                 "Arg_Type", "W_Type", Id_One);

      -----------------------------------
      -- W_Transparent_Type_Definition --
      -----------------------------------

      New_Field (W_Transparent_Type_Definition,
                 "Type_Definition", "W_Type", Id_One);
      Set_Domain (W_Effects, EW_Term);

      ----------------------
      -- W_Record_Binder --
      ----------------------

      New_Field (W_Record_Binder,
                 "Name", "W_Identifier", Id_Lone);
      New_Field (W_Record_Binder,
                 "Arg_Type", "W_Type", Id_One);
      New_Field (W_Record_Binder,
                 "Labels", "Symbol_Set");
      New_Field (W_Record_Binder,
                 "Is_Mutable", "Boolean", "False");

      -------------------------
      -- W_Record_Definition --
      -------------------------

      New_Field (W_Record_Definition,
                 "Fields", "W_Record_Binder", Id_Some);
      Set_Domain (W_Record_Definition, EW_Term);

      -----------------------------
      -- W_Range_Type_Definition --
      -----------------------------

      New_Field (W_Range_Type_Definition, "First", "Uint");
      New_Field (W_Range_Type_Definition, "Last", "Uint");
      Set_Domain (W_Range_Type_Definition, EW_Term);

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

      ---------------
      -- W_Handler --
      ---------------

      New_Field (W_Handler,
                 "Name", "W_Name", Id_One);
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
                 "Labels", "Symbol_Set");
      New_Field (W_Universal_Quantif,
                 "Var_Type", "W_Type", Id_One);
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
                 "Labels", "Symbol_Set");
      New_Field (W_Existential_Quantif,
                 "Var_Type", "W_Type", Id_One);
      New_Field (W_Existential_Quantif,
                 "Pred", "W_Pred", Id_One);

      ---------------
      -- W_Epsilon --
      ---------------

      New_Field (W_Epsilon,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Epsilon,
                 "Typ", "W_Type", Id_One);
      New_Field (W_Epsilon,
                 "Pred", "W_Pred", Id_One);

      -----------
      -- W_Not --
      -----------

      New_Field (W_Not,
                 "Right", "W_Expr", Id_One);

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
                 "Labels", "Symbol_Set");
      New_Field (W_Label,
                 "Def", "W_Expr", Id_One);
      New_Field (W_Label,
                 "Typ", "W_Type", Id_Lone);

      -----------------
      -- W_Loc_Label --
      -----------------

      New_Field (W_Loc_Label, "Sloc", "Source_Ptr");
      New_Field (W_Loc_Label, "Def", "W_Expr", Id_One);
      New_Field (W_Loc_Label, "Marker", "Symbol", "No_Symbol");

      --------------
      -- W_Module --
      --------------

      New_Field (W_Module, "File", "Symbol");
      New_Field (W_Module, "Name", "Symbol");
      Set_Domain (W_Module, EW_Term);

      ------------------
      -- W_Identifier --
      ------------------

      New_Field (W_Identifier, "Name", "W_Name", Id_One);
      New_Field (W_Identifier, "Typ", "W_Type", Id_Lone);
      New_Field (W_Identifier,
                 "Labels", "String_Sets.Set", "String_Sets.Empty_Set");

      --------------
      -- W_Tagged --
      --------------

      New_Field (W_Tagged, "Tag", "Symbol");
      New_Field (W_Tagged, "Def", "W_Expr", Id_One);
      New_Field (W_Tagged, "Typ", "W_Type", Id_Lone);

      ------------
      -- W_Call --
      ------------

      New_Field (W_Call,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Call, "Args", "W_Expr", Id_Set);
      New_Field (W_Call, "Typ", "W_Type", Id_Lone);

      ---------------
      -- W_Literal --
      ---------------

      New_Field (W_Literal, "Value", "EW_Literal");
      New_Field (W_Literal, "Typ", "W_Type", Id_Lone);

      ---------------
      -- W_Binding --
      ---------------

      New_Field (W_Binding,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Binding,
                 "Def", "W_Expr", Id_One);
      New_Field (W_Binding,
                 "Context", "W_Expr", Id_One);
      New_Field (W_Binding, "Typ", "W_Type", Id_Lone);

      -------------
      -- W_Elsif --
      -------------

      New_Field (W_Elsif,
                 "Condition", "W_Expr", Id_One);
      New_Field (W_Elsif,
                 "Then_Part", "W_Expr", Id_One);
      New_Field (W_Elsif,
                 "Typ", "W_Type", Id_Lone);

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
      New_Field (W_Conditional, "Typ", "W_Type", Id_Lone);

      ------------------------
      -- W_Integer_Constant --
      ------------------------

      New_Field (W_Integer_Constant, "Value", "Uint");

      ----------------------
      -- W_Range_Constant --
      ----------------------

      New_Field (W_Range_Constant, "Value", "Uint");
      New_Field (W_Range_Constant, "Typ", "W_Type", Id_One);

      ------------------------
      -- W_Modular_Constant --
      ------------------------

      New_Field (W_Modular_Constant, "Value", "Uint");
      New_Field (W_Modular_Constant, "Typ", "W_Type", Id_One);

      ----------------------
      -- W_Fixed_Constant --
      ----------------------

      New_Field (W_Fixed_Constant, "Value", "Uint");
      New_Field (W_Fixed_Constant, "Typ", "W_Type", Id_One);

      ---------------------
      -- W_Real_Constant --
      ---------------------

      New_Field (W_Real_Constant, "Value", "Ureal");

      ----------------------
      -- W_Float_Constant --
      ----------------------

      New_Field (W_Float_Constant, "Value", "Ureal");
      New_Field (W_Float_Constant, "Typ", "W_Type", Id_One);

      ---------------
      -- W_Comment --
      ---------------

      New_Field (W_Comment,
                 "Comment", "Symbol");

      -------------
      -- W_Deref --
      -------------

      New_Field (W_Deref,
                 "Right", "W_Identifier", Id_One);
      New_Field (W_Deref,
                 "Typ", "W_Type", Id_One);

      ---------------------
      -- W_Record_Access --
      ---------------------

      New_Field (W_Record_Access,
                 "Name", "W_Expr", Id_One);
      New_Field (W_Record_Access,
                 "Field", "W_Identifier", Id_One);
      New_Field (W_Record_Access,
                 "Typ", "W_Type", Id_Lone);

      ---------------------
      -- W_Record_Update --
      ---------------------

      New_Field (W_Record_Update,
                 "Name", "W_Expr", Id_One);
      New_Field (W_Record_Update,
                 "Updates", "W_Field_Association", Id_Some);
      New_Field (W_Record_Update,
                 "Typ", "W_Type", Id_Lone);

      ------------------------
      -- W_Record_Aggregate --
      ------------------------

      New_Field (W_Record_Aggregate,
                 "Associations", "W_Field_Association", Id_Some);
      New_Field (W_Record_Aggregate,
                 "Typ", "W_Type", Id_Lone);

      ----------------
      -- W_Any_Expr --
      ----------------

      New_Field (W_Any_Expr,
                 "Effects", "W_Effects", Id_Lone);
      New_Field (W_Any_Expr,
                 "Pre", "W_Pred", Id_Lone);
      New_Field (W_Any_Expr,
                 "Post", "W_Pred", Id_Lone);
      New_Field (W_Any_Expr,
                 "Return_Type", "W_Type", Id_One);
      New_Field (W_Any_Expr,
                 "Labels", "Symbol_Set");

      ------------------
      -- W_Assignment --
      ------------------

      New_Field (W_Assignment,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Assignment,
                 "Value", "W_Prog", Id_One);
      New_Field (W_Assignment,
                 "Typ", "W_Type", Id_One);
      New_Field (W_Assignment,
                 "Labels", "Symbol_Set");

      -------------------
      -- W_Binding_Ref --
      -------------------

      New_Field (W_Binding_Ref,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Binding_Ref,
                 "Def", "W_Prog", Id_One);
      New_Field (W_Binding_Ref,
                 "Context", "W_Prog", Id_One);
      New_Field (W_Binding_Ref,
                 "Typ", "W_Type", Id_One);

      ------------------
      -- W_While_Loop --
      ------------------

      New_Field (W_While_Loop,
                 "Condition", "W_Prog", Id_One);
      New_Field (W_While_Loop,
                 "Invariants", "W_Pred", Id_Set);
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
      New_Field (W_Abstract_Expr,
                 "Typ", "W_Type", Id_Lone);

      --------------
      -- W_Assert --
      --------------

      New_Field (W_Assert,
                 "Pred", "W_Pred", Id_One);
      New_Field (W_Assert,
                 "Assert_Kind", "EW_Assert_Kind");

      -------------
      -- W_Raise --
      -------------

      New_Field (W_Raise,
                 "Name", "W_Name", Id_One);
      New_Field (W_Raise,
                 "Exn_Type", "W_Type", Id_Lone);
      New_Field (W_Raise,
                 "Typ", "W_Type", Id_Lone);

      -----------------
      -- W_Try_Block --
      -----------------

      New_Field (W_Try_Block,
                 "Prog", "W_Prog", Id_One);
      New_Field (W_Try_Block,
                 "Handler", "W_Handler", Id_Some);
      New_Field (W_Try_Block,
                 "Typ", "W_Type", Id_Lone);

      ---------------------
      -- W_Function_Decl --
      ---------------------

      New_Field (W_Function_Decl,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Function_Decl,
                 "Binders", "W_Binder", Id_Set);
      New_Field (W_Function_Decl,
                 "Effects", "W_Effects", Id_Lone);
      New_Field (W_Function_Decl,
                 "Pre", "W_Pred", Id_Lone);
      New_Field (W_Function_Decl,
                 "Post", "W_Pred", Id_Lone);
      New_Field (W_Function_Decl,
                 "Return_Type", "W_Type", Id_Lone);
      New_Field (W_Function_Decl,
                 "Def", "W_Expr", Id_Lone);
      New_Field (W_Function_Decl,
                 "Labels", "Symbol_Set");
      New_Field (W_Function_Decl,
                 "Location", "Source_Ptr");

      -------------
      -- W_Axiom --
      -------------

      New_Field (W_Axiom,
                 "Name", "Symbol");
      New_Field (W_Axiom,
                 "Def", "W_Pred", Id_One);
      Set_Domain (W_Axiom, EW_Term);

      ------------
      -- W_Goal --
      ------------

      New_Field (W_Goal,
                 "Name", "Symbol");
      New_Field (W_Goal,
                 "Def", "W_Pred", Id_One);
      Set_Domain (W_Goal, EW_Term);

      -----------------
      -- W_Type_Decl --
      -----------------

      New_Field (W_Type_Decl,
                 "Args", "W_Identifier", Id_Set);
      New_Field (W_Type_Decl,
                 "Name", "W_Name", Id_One);
      New_Field (W_Type_Decl,
                 "Labels", "Symbol_Set");
      New_Field (W_Type_Decl,
                 "Definition", "W_Type_Definition", Id_Lone);
      Set_Domain (W_Type_Decl, EW_Term);

      ------------------------------
      -- W_Global_Ref_Declaration --
      ------------------------------

      New_Field (W_Global_Ref_Declaration,
                 "Name", "W_Identifier", Id_One);
      New_Field (W_Global_Ref_Declaration,
                 "Ref_Type", "W_Type", Id_One);
      New_Field (W_Global_Ref_Declaration,
                 "Labels", "Symbol_Set");
      New_Field (W_Global_Ref_Declaration,
                 "Location", "Source_Ptr");
      Set_Domain (W_Global_Ref_Declaration, EW_Prog);

      -----------------------------
      -- W_Exception_Declaration --
      -----------------------------

      New_Field (W_Exception_Declaration,
                 "Name", "W_Name", Id_One);
      New_Field (W_Exception_Declaration,
                 "Arg", "W_Type", Id_Lone);
      Set_Domain (W_Exception_Declaration, EW_Prog);

      -----------------------------
      -- W_Namespace_Declaration --
      -----------------------------

      New_Field (W_Namespace_Declaration,
                 "Declarations", "W_Declaration", Id_Set);
      New_Field (W_Namespace_Declaration,
                 "Name", "Symbol");
      Set_Domain (W_Namespace_Declaration, EW_Prog);

      ---------------------------
      -- W_Include_Declaration --
      ---------------------------

      New_Field (W_Include_Declaration,
                 "Module", "W_Module", Id_One);
      New_Field (W_Include_Declaration,
                 "Kind", "EW_Theory_Type");
      New_Field (W_Include_Declaration,
                 "Use_Kind", "EW_Clone_Type");
      Set_Domain (W_Include_Declaration, EW_Term);

      ------------------------
      -- W_Meta_Declaration --
      ------------------------

      New_Field (W_Meta_Declaration,
                 "Name", "Symbol");
      New_Field (W_Meta_Declaration,
                 "Parameter", "Symbol");
      Set_Domain (W_Meta_Declaration, EW_Term);

      -------------------------
      -- W_Clone_Declaration --
      -------------------------

      New_Field (W_Clone_Declaration,
                 "Origin", "W_Module", Id_One);
      New_Field (W_Clone_Declaration,
                 "As_Name", "Symbol");
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
                 "Orig_Name", "W_Name", Id_One);
      New_Field (W_Clone_Substitution,
                 "Image", "W_Name", Id_One);
      Set_Domain (W_Clone_Substitution, EW_Term);

      --------------------------
      -- W_Theory_Declaration --
      --------------------------

      Set_Mutable (W_Theory_Declaration);
      New_Field (W_Theory_Declaration,
                 "Declarations", "W_Declaration", Id_Set);
      New_Field (W_Theory_Declaration,
                 "Name", "Symbol");
      New_Field (W_Theory_Declaration,
                 "Kind", "EW_Theory_Type");
      New_Field (W_Theory_Declaration,
                 "Includes", "W_Include_Declaration", Id_Set);
      New_Field (W_Theory_Declaration,
                 "Comment", "Symbol");
      Set_Domain (W_Theory_Declaration, EW_Prog);

      ---------------------------
      -- W_Custom_Substitution --
      ---------------------------

      New_Field (W_Custom_Substitution,
                 "From", "Symbol");

      New_Field (W_Custom_Substitution,
                 "To", "W_Any_Node", Id_One);

      --------------------------
      -- W_Custom_Declaration --
      --------------------------

      New_Field (W_Custom_Declaration,
                 "File_Name", "Symbol");

   end Build_AST;

end Xtree_Sinfo;
