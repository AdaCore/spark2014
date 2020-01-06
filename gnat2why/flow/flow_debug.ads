------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                           F L O W _ D E B U G                            --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                Copyright (C) 2013-2020, Altran UK Limited                --
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

--  This package contains debugging code to print various datastructures used
--  by flow analysis in a vaguely human-readable form.

with Common_Containers;    use Common_Containers;
with Flow_Dependency_Maps; use Flow_Dependency_Maps;
with Flow_Types;           use Flow_Types;
with Types;                use Types;

package Flow_Debug is

   procedure Print_Node_Set (S : Node_Sets.Set);
   --  Print a mostly human-readable form the given node set.

   procedure Print_Node_Set (S : Flow_Id_Sets.Set);
   --  Print a mostly human-readable form the given node set.

   procedure Print_Node_Set (S : Ordered_Flow_Id_Sets.Set);
   --  Print a mostly human-readable form the given node set.

   procedure Print_Flow_Map (M : Flow_Id_Maps.Map);
   --  Print a human-readable version of the given map.

   procedure Print_Dependency_Map (Label : String; M : Dependency_Maps.Map);
   --  Print a human-readable form of the given dependency relation.

   procedure Print_Flow_Scope (S : Flow_Scope);
   --  Print a human-readable form of the given scope.

   procedure Sprint_Node_Inline (N : Node_Id);
   --  Print a node on a single line (no EOF is emitted anywhere). Note
   --  this calls Set_Special_Output, so it is not compatible with other
   --  code that calls this.

   procedure pfs (S : Flow_Scope);
   pragma Export (Ada, pfs);
   --  Function for use in GDB. Prints the given flow scope.

end Flow_Debug;
