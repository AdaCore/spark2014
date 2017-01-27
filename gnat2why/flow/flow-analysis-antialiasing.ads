------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--           F L O W . A N A L Y S I S . A N T I A L I A S I N G            --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                  Copyright (C) 2013-2017, Altran UK Limited              --
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

--  This package deals with the detection of aliasing.

package Flow.Analysis.Antialiasing is

   procedure Check_Procedure_Call
     (FA : in out Flow_Analysis_Graphs;
      N  : Node_Id)
   with Pre => Nkind (N) in N_Entry_Call_Statement
                          | N_Procedure_Call_Statement;
   --  This procedure looks at an entry/procedure call statement and
   --  determines if it introduces aliasing that matters: for example
   --  aliasing between in parameters is OK, but aliasing between two
   --  out parameters is not.
   --
   --  This procedure is aware of globals, both computed by gnat2why
   --  and specified by the user. It checks if there is:
   --     * aliasing between any two parameters
   --     * aliasing between a parameter and a global
   --     * potential aliasing between a computed global and abstract state

end Flow.Analysis.Antialiasing;
