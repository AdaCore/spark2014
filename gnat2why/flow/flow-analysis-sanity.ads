------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                 F L O W . A N A L Y S I S . S A N I T Y                  --
--                                                                          --
--                                S p e c                                   --
--                                                                          --
--                  Copyright (C) 2013-2014, Altran UK Limited              --
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

--  This package implements a variety of sanity checks that are run before
--  the rest of flow analysis is performed.

private package Flow.Analysis.Sanity is

   procedure Check_Function_Side_Effects
     (FA   : in out Flow_Analysis_Graphs;
      Sane :    out Boolean);
   --  Make sure no functions with side-effects have been flagged during
   --  analysis.
   --  In debug mode we emit an error message that analysis is aborted here.

   procedure Check_Aliasing
     (FA   : in out Flow_Analysis_Graphs;
      Sane :    out Boolean);
   --  Make sure no aliasing has been flagged during analysis.
   --  In debug mode we emit an error message that analysis is aborted here.

   procedure Check_Variable_Free_Expressions
     (FA   : in out Flow_Analysis_Graphs;
      Sane :    out Boolean);
   --  Enforce SRM 4.4(2): certain expressions must be variable-free

   procedure Check_Illegal_Reads
     (FA   : in out Flow_Analysis_Graphs;
      Sane :    out Boolean);
   --  Enforce SRM 7.1.3(14): a volatile out parameter must never be read from

   procedure Check_Illegal_Writes
     (FA   : in out Flow_Analysis_Graphs;
      Sane :    out Boolean);
   --  Enforce a number of rules concerning illegal updates:
   --     * A package may not update another package's state during elaboration
   --     * An update of a global in

   procedure Check_All_Variables_Known
     (FA   : in out Flow_Analysis_Graphs;
      Sane :    out Boolean);
   --  Sanity check all vertices if they mention a flow id that we do not
   --  know about.

end Flow.Analysis.Sanity;
