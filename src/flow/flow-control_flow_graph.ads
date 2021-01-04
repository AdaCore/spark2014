------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--              F L O W . C O N T R O L _ F L O W _ G R A P H               --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                Copyright (C) 2013-2021, Altran UK Limited                --
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

--  This package will look at a given bit of parse tree and produce
--  the control flow graph (which will then be further processed by
--  other packages under Flow).

package Flow.Control_Flow_Graph is

   procedure Create (FA : in out Flow_Analysis_Graphs);
   --  Produce the control flow graph for the given subprogram body.

end Flow.Control_Flow_Graph;
