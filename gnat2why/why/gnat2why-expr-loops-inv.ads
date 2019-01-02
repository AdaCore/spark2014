------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--               G N A T 2 W H Y - E X P R - L O O P S - I N V              --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2016-2019, AdaCore                     --
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

package Gnat2Why.Expr.Loops.Inv is

   function Generate_Frame_Condition
     (Loop_Stmt          : Node_Id;
      Low_Id             : W_Expr_Id;
      High_Id            : W_Expr_Id;
      Has_Loop_Invariant : Boolean)
      return W_Pred_Id;
   --  Compute the frame condition of a loop statement. For now, only consider
   --  dynamic invariants of modified variables, and the part of the frame
   --  condition that states that unmodified record subcomponents keep their
   --  values around the loop. We also assume values of scalar constants
   --  declared just before the invariant. This is important in particular for
   --  constant introduced by the compiler for the loop invariants themselves.
   --  @param Loop_Stmt considered loop statement.
   --  @param Low_Id identifier for the lower bound of the loop if any.
   --  @param High_Id identifier for the higher bound of the loop if any.
   --  @param Has_Loop_Invariant True iff the loop has a loop invariant.
   --  @return a predicate expression for the loop's frame condition.

end Gnat2Why.Expr.Loops.Inv;
