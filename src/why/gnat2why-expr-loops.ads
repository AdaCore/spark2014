------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                    G N A T 2 W H Y - E X P R - L O O P                   --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2025, AdaCore                     --
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

package Gnat2Why.Expr.Loops is

   function Get_Loop_Invariant
     (Loop_Stmt : N_Loop_Statement_Id)
      return Node_Lists.List;
   --  Return the list of nodes corresponding to loop invariants if any

   function Transform_Exit_Statement
     (Stmt   : N_Exit_Statement_Id;
      Params : Transformation_Params)
      return W_Prog_Id;

   function Transform_Loop_Statement
     (Stmt   : N_Loop_Statement_Id;
      Params : Transformation_Params)
      return W_Prog_Id;

   function Is_In_Loop_Initial_Statements return Boolean with Ghost;
   --  Return True when analyzing the initial statements of a loop

   function Get_Flat_Statement_And_Declaration_List
     (Stmts : List_Id) return Node_Lists.List;
   --  Given a list of statements and declarations Stmts, returns the flattened
   --  list that includes these statements and declarations, and recursively
   --  all inner declarations and statements that appear in block statements
   --  containing a loop invariant.

   function Imprecise_Constant_Value_In_Loop (E : Entity_Id) return Boolean;
   --  Return True if E is a (scalar) constant declared in a loop prior to the
   --  loop invariant whose value is not precisely known at the current program
   --  point.

end Gnat2Why.Expr.Loops;
