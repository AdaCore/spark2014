------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                 F L O W . A N A L Y S I S . S A N I T Y                  --
--                                                                          --
--                                S p e c                                   --
--                                                                          --
--                Copyright (C) 2013-2019, Altran UK Limited                --
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
------------------------------------------------------------------------------

--  This package implements a variety of sanity checks that are run before the
--  rest of flow analysis is performed.

private package Flow.Analysis.Sanity is

   procedure Check_Function_Side_Effects
     (FA   : in out Flow_Analysis_Graphs;
      Sane :    out Boolean);
   --  Make sure no functions with side-effects have been flagged during
   --  analysis.
   --  In debug mode we emit an error message that analysis is aborted here.

   procedure Check_Expressions
     (FA   : in out Flow_Analysis_Graphs;
      Sane :    out Boolean);
   --  Emits errors:
   --     * Enforce SRM 4.4(2): certain expressions must be variable-free
   --
   --  Emits high checks:
   --     * Enforce SRM 7.3.2(4): no calls to boundary subprograms in
   --                             invariants
   --
   --  Sane is set to true if no *errors* have been emitted, but note this
   --  subprogram may raise checks.

   procedure Check_Illegal_Writes
     (FA   : in out Flow_Analysis_Graphs;
      Sane :    out Boolean);
   --  Enforce a number of rules concerning illegal updates:
   --     * A package may not update another package's state during elaboration
   --     * An update of a global in

   procedure Check_All_Variables_Known
     (FA   : in out Flow_Analysis_Graphs;
      Sane :    out Boolean);
   --  Sanity check all vertices if they mention a flow id that we do not know
   --  about.

   procedure Check_Generated_Refined_Global
     (FA   : in out Flow_Analysis_Graphs;
      Sane :    out Boolean);
   --  Checks if the generated Refined_Global contract is correct with respect
   --  to the user-provided Global/Depends contract.

   procedure Check_Side_Effects_In_Protected_Functions
     (FA   : in out Flow_Analysis_Graphs;
      Sane :    out Boolean);
   --  Checks for side effects in protected functions. It detects functions
   --  that make uses of volatile variables with Effective_Reads and which are
   --  declared as Part_Of the PO. Issues an error message when this happens.
   --
   --  In Flow.Control_Flow_Graphs a similar check is carried on. In
   --  particular, there we detect uses of volatile variables with
   --  Effective_Reads which are globals of the analyzed subprogram. In the
   --  case of a protected function that uses a volatile variable with
   --  Effective_Reads and which is declared as Part_Of the protected object,
   --  the variable is no longer seen as a global and therefore we need this
   --  extra check.

end Flow.Analysis.Sanity;
