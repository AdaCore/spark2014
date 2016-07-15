------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                 F L O W . A N A L Y S I S . S A N I T Y                  --
--                                                                          --
--                                S p e c                                   --
--                                                                          --
--                  Copyright (C) 2013-2016, Altran UK Limited              --
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

   procedure Check_Variable_Free_Expressions
     (FA   : in out Flow_Analysis_Graphs;
      Sane :    out Boolean);
   --  Enforce SRM 4.4(2): certain expressions must be variable-free

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
   --  to the user-provided Global contract.

   procedure Check_Part_Of
     (FA   : in out Flow_Analysis_Graphs;
      Sane :    out Boolean);
   --  The front-end enforces Part_Of on hidden state in all cases except for
   --  constants, since it cannot tell between a constant with variable input
   --  (which needs Part_Of) and one without (which does not).
   --
   --  This checks if there is any missing Part_Of indicator for constants with
   --  variable input that are:
   --  * declared immidiately within the private part of a given package
   --  * part of the visible state of a package that is declared immediately
   --    within the private part of a given package.
   --
   --  Note that deferred constants are exempt since they are visible and thus
   --  are not hidden state.

end Flow.Analysis.Sanity;
