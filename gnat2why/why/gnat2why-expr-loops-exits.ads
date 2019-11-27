------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--             G N A T 2 W H Y - E X P R - L O O P S - E X I T S            --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2018-2019, AdaCore                     --
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

--  This unit deals with the special treatment of exit paths inside loops.
--  Because Why3 VC generation includes all effects syntactically occurring
--  inside the loop in the computed loop effects, even on path that exit the
--  loop, we extract such paths from the loop so that the corresponding effects
--  are not counted in the loop effects.
--
--  This increases the precision of the analysis and removes the need for
--  manual loop invariants stating some variables are not modified throughout
--  the loop.
--
--  Only paths that have at least one instruction in addition to the
--  unconditional exit or return are extracted. The loop is translated as
--  usual, with the exit paths being replaced by raising an exception, which
--  is later caught to apply the instructions from the exit path.

with Nlists; use Nlists;

package Gnat2Why.Expr.Loops.Exits is

   procedure Before_Start_Of_Loop;
   --  Initialization procedure to call before start of loop handling.
   --  This should be followed by a call to [Wrap_Loop_Body] to pop up
   --  the corresponding context.

   procedure Record_And_Replace
     (Instrs : List_Id;
      Expr   : in out W_Prog_Id)
   with Pre => List_Length (Instrs) > 0;
   --  @param Instr List of statements or declarations
   --  @param Expr Translation of the list into Why3
   --  When relevant, create a new exception and replace [Expr] by raising
   --  this new exception. In that case, the mapping from the exception and
   --  the original Why3 program is stored.

   procedure Wrap_Loop_Body (Loop_Body : in out W_Prog_Id);
   --  Wrap loop body program in a try-block if needed, to deal with statements
   --  occurring before exit statements inside the loop body.

end Gnat2Why.Expr.Loops.Exits;
