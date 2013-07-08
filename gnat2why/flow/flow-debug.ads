------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                           F L O W . D E B U G                            --
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

--  This package contains debugging code to print various
--  datastructures used by flow analysis in a vaguely human-readable
--  form.

package Flow.Debug is

   procedure Print_Node_Set (S : Flow_Id_Sets.Set);
   --  Print a mostly human-readable form the given node set.

   procedure Print_Dependency_Map (M : Dependency_Maps.Map);
   --  Print a human-readable form of the given dependency relation.

   procedure Print_Optional_Dependency_Map (M : Optional_Dependency_Maps.Map);
   --  Print a human-readable form of the given dependency relation.

end Flow.Debug;
