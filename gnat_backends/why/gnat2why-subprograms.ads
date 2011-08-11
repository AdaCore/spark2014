------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   G N A T 2 W H Y - S U B P R O G R A M S                --
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

with Types;         use Types;
with Why.Ids;       use Why.Ids;
with Why.Inter;     use Why.Inter;

package Gnat2Why.Subprograms is

   --  This package deals with the translation of GNAT functions and
   --  statements to Why declarations.

   --  There is one main distinction to make: the one between functions and
   --  procedures.
   --
   --  Here in the Gnat2Why backend, we assume that all functions are
   --  side effect free expression functions. All other functions have been
   --  translated to procedures. We also currently assume that no recursion
   --  exists. This means that we can translate such functions into Why
   --  logical functions.
   --  TBD: Do expression functions have a contract? We don't need one, but if
   --  there is one, what to do with it?

   --  Procedures are translated to Why programs with pre- and postconditions
   --  (contracts). These assertions are strengthened to enforce the same
   --  semantics as if these assertions were executed. For example, an array
   --  access like
   --     X (I) = 0
   --  is protected by a condition:
   --     I in X'First .. X'Last and then X (I) = 0.
   --  To do this, we use the generic functions that exist in the GNAT
   --  frontend.
   --
   --  Procedure contracts may contain calls to expression functions. As we
   --  have translated these functions to Why logic functions, nothing special
   --  needs to be done.
   --
   --  Why actually contains two languages: The logic language for assertions
   --  and logical functions and the programming language for programs with
   --  side effects. Programs may contain assertions, for example as pre- and
   --  postconditions. We call the elements of the logic language "(logic)
   --  terms" while we call the elements of the programming language
   --  "(program) expressions".  There are no statements in the Why language;
   --  statements are simply expressions of the type "unit".
   --
   --  We need two functions to deal with Ada expressions: one to translate
   --  them to logic terms (the body of Ada expression functions) and one to
   --  translate them to program expressions. As logic terms are allowed in
   --  program expressions, an Ada expression should be preferentially
   --  translated to a logic term whenever possible.  Ada Statements can only
   --  occur in Ada procedures and are translated to program expressions only.
   --
   --  More specific documentation is given at the beginning of each function
   --  in this package.

   function Get_Range (N : Node_Id) return Node_Id;
   --  Get the range of a range constraint or subtype definition.
   --  The return node is of kind N_Range

   function Type_Of_Node (N : Node_Id) return String;
   --  Get the name of the type of an Ada node, as a string

   function Type_Of_Node (N : Node_Id) return Entity_Id;
   --  Get the name of the type of an Ada node, as a Node_Id of Kind
   --  N_Defining_Identifier

   function Type_Of_Node (N : Node_Id) return Why_Type;
   --  Get the name of the type of an Ada node, as a Why Type

   procedure Why_Decl_Of_Ada_Subprogram
     (File    : W_File_Id;
      Node    : Node_Id;
      As_Spec : Boolean);
   --  Generate a Why declaration that corresponds to an Ada subprogram
   --  Node is a N_Subprogram_Body
   --
   --  Care must be taken in a few cases:
   --  * We need to add an argument of type "unit" if the Ada subprogram has
   --    no parameters
   --  * The types of arguments have to be references
   --  * The pre/postconditions need special treatment (TCC)

   function Why_Expr_Of_Ada_Stmt (Stmt : Node_Id) return W_Prog_Id;
   --  Translate a single Ada statement into a Why expression

   function Why_Predicate_Of_Ada_Expr (Expr : Node_Id) return W_Predicate_Id;
   --  Translate an Ada Expression to a Why predicate

   function Why_Term_Of_Ada_Expr
     (Expr          : Node_Id;
      Expected_Type : Why_Type) return W_Term_Id;
   --  Translate an Ada Expression to a Why Term of the Expected_Type.

   function Why_Term_Of_Ada_Expr (Expr : Node_Id) return W_Term_Id;

end Gnat2Why.Subprograms;
