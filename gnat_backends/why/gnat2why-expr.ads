------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        G N A T 2 W H Y - E X P R                         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2012, AdaCore                   --
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

with Ada.Containers.Hashed_Maps;

with Types;          use Types;

with Why.Types;      use Why.Types;
with Why.Ids;        use Why.Ids;
with Why.Inter;      use Why.Inter;
with Why.Sinfo;      use Why.Sinfo;

with Gnat2Why.Nodes; use Gnat2Why.Nodes;
with Gnat2Why.Util;  use Gnat2Why.Util;

package Gnat2Why.Expr is

   Container_Type_To_Has_Element_Function : Node_Maps.Map;
   --  Map of entities, from container's type to the corresponding Has_Element
   --  function.

   function Assignment_Of_Obj_Decl (N : Node_Id) return W_Prog_Id;
   --  Generate an assignment from an object declaration

   function Assume_Of_Scalar_Subtype
     (Params : Transformation_Params;
      N      : Entity_Id;
      Base   : Entity_Id) return W_Prog_Id;

   function Assume_Of_Subtype_Indication
     (Params : Transformation_Params;
      N      : Node_Id) return W_Prog_Id;

   function Get_Pure_Logic_Term_If_Possible
     (File          : Why_File;
      Expr          : Node_Id;
      Expected_Type : W_Base_Type_Id) return W_Term_Id;
   --  If Expr can be translated into a pure logic term (without dereference),
   --  return this term. Otherwise, return Why_Empty.

   function Range_Expr
     (N           : Node_Id;
      T           : W_Expr_Id;
      Domain      : EW_Domain;
      Params      : Transformation_Params;
      T_Type      : W_Base_Type_OId := Why_Empty) return W_Expr_Id;
   --  Given an N_Range node N and a Why expr T, create an expression
   --  low <= T <= high
   --  where "low" and "high" are the lower and higher bounds of N.
   --  T_Type is the base type in which the comparisons take
   --  place (e.g. int, real). If it is not set, it is deduced from
   --  the bounds' type.

   function Has_Element_Expr
     (Cont   : Node_Id;
      Cursor : W_Expr_Id;
      Domain : EW_Domain;
      Params : Transformation_Params) return W_Expr_Id;
   --  Return an expression that constrains Cursor to belong to container Cont:
   --     Has_Element (Cont, Cursor)

   function Get_Container_In_Iterator_Specification
     (N : Node_Id) return Node_Id;

   procedure Transform_Pragma_Check
     (Stmt    : Node_Id;
      Runtime : out W_Prog_Id;
      Pred    : out W_Pred_Id);
   --  Given a pragma Check in Stmt, generates the corresponding proposition in
   --  Pred, and the program which checks the absence of run-time errors in
   --  Runtime.

   function Transform_Discrete_Choices
     (Case_N       : Node_Id;
      Matched_Expr : W_Expr_Id;
      Cond_Domain  : EW_Domain;
      Params       : Transformation_Params) return W_Expr_Id;
      --  Return the guard that corresponds to a branch

   function Transform_Attribute_Old
     (Expr   : Node_Id;
      Domain : EW_Domain;
      Params : Transformation_Params) return W_Expr_Id;
   --  Translate Expr'Old into Why

   function Transform_Expr
     (Expr          : Node_Id;
      Expected_Type : W_Base_Type_Id;
      Domain        : EW_Domain;
      Params        : Transformation_Params) return W_Expr_Id;
   --  Compute an expression in Why having the expected type for the given Ada
   --  expression node. The formal "Domain" decides if we return a predicate,
   --  term or program. If Ref_Allowed is True, then references are allowed,
   --  for example in the context of a program (whether the domain is EW_Prog
   --  for program text or EW_Pred/EW_Term for contract). If Ref_Allowed is
   --  False, then references are not allowed, for example in the context of an
   --  axiom or a logic function definition.

   function Transform_Expr
     (Expr        : Node_Id;
      Domain      : EW_Domain;
      Params      : Transformation_Params) return W_Expr_Id;
   --  Same as above, but derive the Expected_Type from the Ada Expr

   function Transform_Expr_With_Actions
     (Expr          : Node_Id;
      Actions       : List_Id;
      Expected_Type : W_Base_Type_Id;
      Domain        : EW_Domain;
      Params        : Transformation_Params) return W_Expr_Id;
   --  Same as Transform_Expr, but takes into account the declarations of
   --  constants in Actions, to create a suitable variable map for translating
   --  Expr.

   function Transform_Expr_With_Actions
     (Expr          : Node_Id;
      Actions       : List_Id;
      Domain        : EW_Domain;
      Params        : Transformation_Params) return W_Expr_Id;
   --  Same as above, but derive the Expected_Type from the Ada Expr

   function Transform_Statements (Stmts : List_Of_Nodes.List) return W_Prog_Id;
   function Transform_Statements (Stmts : List_Id) return W_Prog_Id;
   --  Transforms a list of statements into a Why expression. An empty list is
   --  transformed into the void expression.

   function Transform_Statements
     (Cur_Stmt  : Node_Id;
      Prev_Prog : W_Prog_Id) return W_Prog_Id;
   --  Transform the next statement Cur_Stmt in a list of statements, where
   --  Prev_Prog is the transformation of the previous statements in the list.
   --  This allows treating the case where Cur_Stmt is a pragma Assert_And_Cut.

   function Transform_Declarations_Block (L : List_Id; Core : W_Prog_Id)
      return W_Prog_Id;
   --  Translate the Declarations block of Block statement or subprogram to a
   --  sequence of Why expressions; dynamic type declarations are translated
   --  to assert/assume statements, object declarations to assignment
   --  statements

   ----------------------------------------
   -- Attributes Old, Loop_Entry, Result --
   ----------------------------------------

   --  Expressions X'Old and F'Result are normally expanded into references to
   --  saved values of variables by the frontend, but this expansion does not
   --  apply to the original postcondition. It is this postcondition which
   --  is translated by gnat2why into a program to detect possible run-time
   --  errors, therefore a special mechanism is needed to deal with expressions
   --  X'Old and F'Result.

   Result_Name : W_Identifier_Id := Why_Empty;
   --  Name to use for occurrences of F'Result in the postcondition. It should
   --  be equal to Why_Empty when we are not generating code for detecting
   --  run-time errors in the postcondition.

   package Old_Nodes is new Ada.Containers.Hashed_Maps
     (Key_Type        => Node_Id,
      Element_Type    => W_Identifier_Id,
      Hash            => Node_Hash,
      Equivalent_Keys => "=",
      "="             => "=");

   package Loop_Entry_Nodes is new Ada.Containers.Hashed_Maps
     (Key_Type        => Node_Id,
      Element_Type    => Old_Nodes.Map,
      Hash            => Node_Hash,
      Equivalent_Keys => "=",
      "="             => Old_Nodes."=");

   function Bind_From_Mapping_In_Expr
     (Params : Transformation_Params;
      Map    : Old_Nodes.Map;
      Expr   : W_Prog_Id) return W_Prog_Id;
   --  Bind names from Map to their corresponding values, obtained by
   --  transforming the expression node associated to the name in Map, in Expr.

   function Name_For_Loop_Entry
     (Expr    : Node_Id;
      Loop_Id : Node_Id) return W_Identifier_Id;
   --  Returns the identifier to use for a Expr'Loop_Entry(Loop_Id)

   function Map_For_Loop_Entry (Loop_Id : Node_Id) return Old_Nodes.Map;
   --  Returns the map of identifiers to use for Loop_Entry attribute
   --  references applying to loop Loop_Id.

   function Map_For_Old return Old_Nodes.Map;
   --  Returns the map of identifiers to use for Old attribute references in
   --  the current subprogram.

   procedure Reset_Map_For_Old;
   --  Empty the map of identifiers to use for Old attribute references

   function Name_For_Old (N : Node_Id) return W_Identifier_Id;
   --  During the generation of code for detecting run-time errors in the
   --  postcondition, return the name to use for occurrences of N'Old.

   --  Register a node that appears with attribute 'Old; return a fresh
   --  Name_Id for this Node. This function is intended to be called by the
   --  code that translates expressions to Why (Gnat2why.Expr), which itself
   --  is called by Transform_Subprogram. For each call to this
   --  function, a declaration at the beginning of the Why program is
   --  generated.

   function Name_For_Result return W_Identifier_Id;
   --  During the generation of code for detecting run-time errors in the
   --  postcondition of F, return the name to use for occurrences of F'Result.

private
   --  Mapping of all expressions whose 'Old attribute is used in the current
   --  postcondition to the translation of the corresponding
   --  expression in Why. Until 'Old is forbidden in the body, this is also
   --  used to translate occurrences of 'Old that are left by the frontend (for
   --  example, inside quantified expressions that are only preanalyzed).
   --
   --  The mapping is cleared before generating Why code for VC generation for
   --  the body and postcondition, filled during the translation, and used
   --  afterwards to generate the necessary copy instructions.

   Old_Map        : Old_Nodes.Map;
   Loop_Entry_Map : Loop_Entry_Nodes.Map;

   function Map_For_Loop_Entry (Loop_Id : Node_Id) return Old_Nodes.Map is
     (if Loop_Entry_Map.Contains (Loop_Id) then
        Loop_Entry_Map.Element (Loop_Id)
      else
        Old_Nodes.Empty_Map);

   function Map_For_Old return Old_Nodes.Map is (Old_Map);

end Gnat2Why.Expr;
