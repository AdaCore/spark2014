------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                            W H Y - S I N F O                             --
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

package Why.Sinfo is
   pragma Pure;

   --  This package defines the structure of the abstract syntax tree.
   --  It does not strictly follow the Why syntax though; there is
   --  usually one entity for both program space and logic space, even if
   --  they are expressed with a different syntax in the generated Why code.
   --  This aims at reducing code duplication.
   --  For more info about the syntax tree, see xgen/xtree_sinfo.adb

   type Why_Node_Kind is
     (
      W_Unused_At_Start,

      -----------
      -- Types --
      -----------

      W_Base_Type,
      W_Abstract_Type,
      W_Generic_Formal_Type,
      W_Generic_Actual_Type_Chain,
      W_Array_Type,
      W_Ref_Type,
      W_Computation_Type,

      --------------------
      -- Type structure --
      --------------------

      W_Effects,
      W_Binder,
      W_Transparent_Type_Definition,
      W_Adt_Definition,
      W_Constr_Decl,

      -------------------------
      -- Predicate structure --
      -------------------------

      W_Triggers,
      W_Trigger,
      W_Pattern,
      W_Match_Case,

      --------------------
      -- Prog structure --
      --------------------

      W_Postcondition,
      W_Exn_Condition,
      W_Loop_Annot,
      W_Wf_Arg,
      W_Handler,

      -----------------
      -- Preds, Expr --
      -----------------

      W_Universal_Quantif,
      W_Existential_Quantif,

      ------------------------
      -- Preds, Progs, Expr --
      ------------------------

      W_Not,
      W_Relation,
      W_Connection,
      W_Label,

      -------------------------------
      -- Preds, Terms, Progs, Expr --
      -------------------------------

      W_Identifier,
      W_Call,
      W_Literal,
      W_Binding,
      W_Conditional,

      -------------------------
      -- Terms, Progs, Exprs --
      -------------------------

      W_Integer_Constant,
      W_Real_Constant,
      W_Void,
      W_Binary_Op,
      W_Unary_Op,
      W_Match,
      W_Array_Access,
      W_Epsilon,

      -----------------
      -- Progs, Expr --
      -----------------

      W_Any_Expr,
      W_Assignment,
      W_Array_Update,
      W_Binding_Ref,
      W_While_Loop,
      W_Statement_Sequence,
      W_Assert,
      W_Raise,
      W_Try_Block,
      W_Unreachable_Code,

      ----------------------------
      -- Top-level declarations --
      ----------------------------

      W_Function_Decl,
      W_Function_Def,
      W_Axiom,
      W_Goal,
      W_Type,
      W_Global_Ref_Declaration,
      W_Exception_Declaration,
      W_Include_Declaration,
      W_Clone_Declaration,
      W_Clone_Substitution,

      -----------------
      -- Input files --
      -----------------

      W_File

      );

   type EW_ODomain is
     (EW_Expr,
      EW_Term,
      EW_Pred,
      EW_Prog);

   subtype EW_Domain is EW_ODomain range
       EW_Term ..
   --  EW_Pred
       EW_Prog;

   type EW_Type is
     (EW_Unit,
      EW_Prop,
      EW_Bool,
      EW_Int,
      EW_Real,
      EW_Abstract);

   subtype EW_Not_Null_Type is EW_Type range
       EW_Prop ..
   --  EW_Bool
   --  EW_Int
   --  EW_Real
       EW_Abstract;

   subtype EW_Term_Type is EW_Not_Null_Type range
       EW_Bool ..
   --  EW_Int
   --  EW_Real
       EW_Abstract;

   subtype EW_Base_Type is EW_Type range
       EW_Unit ..
   --  EW_Prop
   --  EW_Bool
   --  EW_Int
       EW_Real;

   subtype EW_Scalar is EW_Base_Type range
       EW_Bool ..
   --  EW_Int
       EW_Real;

   subtype EW_Numeric is EW_Base_Type range
       EW_Int ..
       EW_Real;

   type EW_Literal is
     (EW_True,
      EW_False);

   type EW_Binary_Op is
     (EW_Add,
      EW_Substract,
      EW_Multiply,
      EW_Divide,
      EW_Mod);

   type EW_Relation is
     (EW_None,
      EW_Eq,
      EW_Ne,
      EW_Lt,
      EW_Le,
      EW_Gt,
      EW_Ge);

   type EW_Clone_Type is
      (EW_Import,
       EW_Export,
       EW_Clone_Default);

   type EW_Subst_Type is
      (EW_Type_Subst,
       EW_Function,
       EW_Namepace,
       EW_Lemma,
       EW_Goal);

   type EW_Connector is
     (EW_Or_Else,
      EW_And_Then,
      EW_Imply,
      EW_Equivalent,
      EW_Or,
      EW_And);

   type EW_Unary_Op is (EW_Minus, EW_Deref);

end Why.Sinfo;
