------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                           F L O W . S A N I T Y                          --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                Copyright (C) 2018-2019, Altran UK Limited                --
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

--  Routines that belong to flow analysis, but are applied not only to the
--  current compilation unit.

package Flow_Sanity is

   procedure Check_Incomplete_Globals;
   --  A sanity check for all translated routines, as the flow analysis only
   --  flags mismatches between Pre/Post and Global/Depends contracts for
   --  routines from the current compilation unit with bodies in SPARK;
   --  however, proof expects that the Global/Depends will introduce at least
   --  the globals referenced in Pre/Post, as otherwise we will crash with an
   --  illegal .mlw file.

end Flow_Sanity;
