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
with Why.Inter;     use Why.Inter;
with Why.Sinfo;     use Why.Sinfo;

package Gnat2Why.Expr is

   function Assignment_of_Obj_Decl (N : Node_Id) return W_Prog_Id;
   --  Generate an assignment from an object declaration

   function Why_Ident_Of_Ada_Ident (Id : Node_Id) return W_Identifier_Id;
   --  Build a Why identifier out of an Ada Node.

   function Why_Expr_Of_Ada_Expr
     (Expr          : Node_Id;
      Expected_Type : Why_Type;
      Domain        : EW_Domain) return W_Expr_Id;
   --  Compute an expression in Why having the expected type for the given Ada
   --  expression node. The formal "Domain" decides if we return a predicate,
   --  term or program

   function Why_Expr_Of_Ada_Expr (Expr : Node_Id; Domain : EW_Domain)
      return W_Expr_Id;
   --  Same as above, but derive the Expected_Type from the Ada Expr

   function Why_Expr_Of_Ada_Stmt (Stmt : Node_Id) return W_Prog_Id;
   --  Translate a single Ada statement into a Why expression

   function Why_Expr_Of_Ada_Stmts
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

   function Type_Of_Node (N : Node_Id) return Why_Type;
   --  Get the name of the type of an Ada node, as a Why Type

   function Get_Range (N : Node_Id) return Node_Id
      with Post =>
         (Present (Low_Bound (Get_Range'Result)) and then
          Present (High_Bound (Get_Range'Result)));
   --  Get the range of a range constraint or subtype definition.
   --  The return node is of kind N_Range

end Gnat2Why.Expr;
