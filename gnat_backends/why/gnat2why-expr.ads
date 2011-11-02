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

   function Assume_of_Integer_Subtype (E : Entity_Id) return W_Prog_Id;

   function Assume_of_Integer_Subtype
      (N    : Entity_Id;
       Base : Entity_Id) return W_Prog_Id;

   function Assume_of_Subtype_Indication (N : Node_Id) return W_Prog_Id;

   function Get_Pure_Logic_Term_If_Possible
     (Expr          : Node_Id;
      Expected_Type : W_Base_Type_Id) return W_Term_Id;
   --  If Expr can be translated into a pure logic term (without dereference),
   --  return this term. Otherwise, return Why_Empty.

   function Range_Expr
     (N           : Node_Id;
      T           : W_Expr_Id;
      Domain      : EW_Domain;
      Ref_Allowed : Boolean) return W_Expr_Id;
   --  Given an N_Range node N and a Why expr T, create an expression
   --  low <= T <= high
   --  where "low" and "high" are the lower and higher bounds of N.

   function Transform_Ident (Id : Node_Id) return W_Identifier_Id;
   --  Build a Why identifier out of an Ada Node.

   function Transform_Pragma_Check (Stmt : Node_Id; Runtime : out W_Prog_Id)
      return W_Pred_Id;
   --  Translate a pragma check into a predicate; also, generate an expression
   --  which will make generate the necessary checks for Why

   function Transform_Expr
     (Expr          : Node_Id;
      Expected_Type : W_Base_Type_Id;
      Domain        : EW_Domain;
      Ref_Allowed   : Boolean) return W_Expr_Id;
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
      Ref_Allowed : Boolean) return W_Expr_Id;
   --  Same as above, but derive the Expected_Type from the Ada Expr

   function Transform_Statements
     (Stmts      : List_Id;
      Start_From : Node_Id := Empty)
     return W_Prog_Id;
   --  Translate a list of Ada statements into a single Why expression.
   --  An empty list is translated to "void".
   --  The parameter Start_From indicates a node in the list from which the
   --  translation process is to be started. All nodes before and including
   --  Start_From are ignored.

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
