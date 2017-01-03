------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                                 F L O W                                  --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                 Copyright (C) 2016-2017, Altran UK Limited               --
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

with Ada.Containers.Multiway_Trees;

package Flow_Generated_Globals.Traversal is

   package Node_Trees is new Ada.Containers.Multiway_Trees
     (Element_Type => Entity_Id,
      "="          => "=");

   subtype Tree_Cursor is Node_Trees.Cursor;
   --  Alias for tree scope tree cursor

   procedure Build_Tree (CU : Node_Id);
   --  Traverse compilation unit CU to build traversal tree

   procedure Iterate
     (Process : not null access procedure (E : Entity_Id));
   --  Post-order iterate the hierarchical container with entities processed by
   --  the flow analysis, i.e. packages, functions, procedures, entries, task
   --  types and protected types.

   function Root_Entity return Tree_Cursor;
   --  Returns a cursor for the root scope; for custom iteration

end Flow_Generated_Globals.Traversal;
