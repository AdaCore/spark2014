------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                        F L O W . A N A L Y S I S                         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                  Copyright (C) 2013, Altran UK Limited                   --
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

--  This package looks at the produced graphs and emits error
--  messages.

package Flow.Analysis is

   procedure Analyse_Main (FA : Flow_Analysis_Graphs);
   --  If FA corresponds to a main program, we ensure that
   --  all globals it references are initialised.

   procedure Sanity_Check (FA   : Flow_Analysis_Graphs;
                           Sane : out Boolean);
   --  Check the following basic properties:
   --     - is aliasing present (using the flag FA.Aliasing_Present)?
   --     - do we somehow depend on a record with non-manifest constant
   --       default initializations?
   --     - are all global variables used declared as such?
   --
   --  Complexity is O(N)

   procedure Find_Ineffective_Imports (FA : Flow_Analysis_Graphs);
   --  Find all ineffective initial values.
   --
   --  Complexity is O(N^2)

   procedure Find_Illegal_Updates (FA : Flow_Analysis_Graphs);
   --  Find all cases where we update an in parameter or global.
   --
   --  Complexity is O(N)
   --
   --  !!! this should be moved to spark_definition

   procedure Find_Ineffective_Statements (FA : Flow_Analysis_Graphs);
   --  Find all ineffective statements.
   --
   --  Complexity is O(N^2)

   procedure Find_Use_Of_Uninitialised_Variables (FA : Flow_Analysis_Graphs);
   --  Find all instances where uninitialised variables are used. Two
   --  separate checks are performed.
   --
   --  Complexity is O(N)

   procedure Find_Stable_Elements (FA : Flow_Analysis_Graphs);
   --  Find stable loop statements.
   --
   --  Complexity is O(N^2)

   procedure Find_Unused_Objects (FA : Flow_Analysis_Graphs);
   --  Find unused objects.
   --
   --  Complexity is O(N)

   procedure Check_Contracts (FA : Flow_Analysis_Graphs);
   --  Check the given depends against the reality. If there is no
   --  depends aspect this procedure does nothing.
   --
   --  Complexity is O(N^2)

end Flow.Analysis;
