------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                    G N A T 2 W H Y - E X P R - L O O P                   --
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

package Gnat2Why.Expr.Loops is

   function Get_Loop_Invariant (Loop_Stmt : Node_Id) return Node_Lists.List;
   --  Return the list of nodes corresponding to loop invariants if any

   function Transform_Exit_Statement (Stmt : Node_Id) return W_Prog_Id
   with Pre => Nkind (Stmt) = N_Exit_Statement;

   function Transform_Loop_Statement (Stmt : Node_Id) return W_Prog_Id
   with Pre => Nkind (Stmt) = N_Loop_Statement;

   function Is_In_Loop_Initial_Statements return Boolean with Ghost;
   --  Return True when analyzing the initial statements of a loop

end Gnat2Why.Expr.Loops;
