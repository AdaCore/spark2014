------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        G N A T 2 W H Y - E X P R                         --
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

with Atree;         use Atree;
with Sinfo;         use Sinfo;
with Types;         use Types;
with Why.Ids;       use Why.Ids;
with Why.Sinfo;     use Why.Sinfo;

package Gnat2Why.Expr is

   function Assignment_of_Obj_Decl (N : Node_Id) return W_Prog_Id;
   --  Generate an assignment from an object declaration

   function Range_Expr (N : Node_Id; T : W_Expr_Id; Domain : EW_Domain)
      return W_Expr_Id;
   --  Given an N_Range node N and a Why expr T, create an expression
   --  low <= T <= high
   --  where "low" and "high" are the lower and higher bounds of N.

   function Transform_Ident (Id : Node_Id) return W_Identifier_Id;
   --  Build a Why identifier out of an Ada Node.

   function Predicate_Of_Pragma_Check (N : Node_Id) return W_Pred_Id;
   --  Compute a Why predicate from a node of kind Pragma Check. Raise
   --  Not_Implemented if it is not a Pragma Check.

   function Transform_Expr
     (Expr          : Node_Id;
      Expected_Type : W_Base_Type_Id;
      Domain        : EW_Domain) return W_Expr_Id;
   --  Compute an expression in Why having the expected type for the given Ada
   --  expression node. The formal "Domain" decides if we return a predicate,
   --  term or program

   function Transform_Expr (Expr : Node_Id; Domain : EW_Domain)
      return W_Expr_Id;
   --  Same as above, but derive the Expected_Type from the Ada Expr

   function Transform_Static_Expr
     (Expr          : Node_Id;
      Expected_Type : W_Base_Type_Id) return W_Term_Id;
   --  If Expr is static, return a term equivalent to Expr. Otherwise,
   --  return Why_Empty.

   function Transform_Statements
     (Stmts      : List_Id;
      Start_From : Node_Id := Empty)
     return W_Prog_Id;
   --  Translate a list of Ada statements into a single Why expression.
   --  An empty list is translated to "void".
   --  The parameter Start_From indicates a node in the list from which the
   --  translation process is to be started. All nodes before and including
   --  Start_From are ignored.

   function Transform_Component_Associations
     (Domain : EW_Domain;
      CA     : List_Id)
     return W_Expr_Array;

   function Type_Of_Node (N : Node_Id) return String;
   --  Get the name of the type of an Ada node, as a string

   function Type_Of_Node (N : Node_Id) return Entity_Id;
   --  Get the name of the type of an Ada node, as a Node_Id of Kind
   --  N_Defining_Identifier

   function Type_Of_Node (N : Node_Id) return W_Base_Type_Id;
   --  Get the name of the type of an Ada node, as a Why Type

   function Get_Range (N : Node_Id) return Node_Id
      with Post =>
         (Present (Low_Bound (Get_Range'Result)) and then
          Present (High_Bound (Get_Range'Result)));
   --  Get the range of a range constraint or subtype definition.
   --  The return node is of kind N_Range

end Gnat2Why.Expr;
