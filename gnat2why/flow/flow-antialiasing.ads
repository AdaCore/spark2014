------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                    F L O W . A N T I A L I A S I N G                     --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                  Copyright (C) 2013-2015, Altran UK Limited              --
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

with Sinfo; use Sinfo;

package Flow.Antialiasing is

   procedure Check_Procedure_Call
     (N                   : Node_Id;
      Introduces_Aliasing : in out Boolean)
   with Pre => Nkind (N) = N_Procedure_Call_Statement;
   --  This procedure looks at a procedure call statement and
   --  determines if it introduces aliasing that matters: for example
   --  aliasing between in parameters is OK, but aliasing between two
   --  out parameters is not.
   --
   --  If aliasing is detected two actions are taken:
   --     * A flow error is emitted
   --     * The flag Introduces_Aliasing is set to True (otherwise its
   --       value is not changed)
   --
   --  This procedure is aware of globals, both computed by gnat2why
   --  and specified. The following checks are performed:
   --     * Is there aliasing between any two parameters
   --     * Is there aliasing between a parameter and a global
   --     * Is there potential aliasing between a computed global and
   --       abstract state

end Flow.Antialiasing;
