------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                     F L O W _ V I S I B I L I T Y                        --
--                                                                          --
--                                S p e c                                   --
--                                                                          --
--                Copyright (C) 2018-2020, Altran UK Limited                --
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

with Atree;         use Atree;
with Flow_Types;    use Flow_Types;
with Gnat2Why_Args;
with Types;         use Types;

package Flow_Visibility is

   --  The visibility graph is created in two passes: first vertices, then
   --  edges, because frontend doesn't provide a realiable routine that would
   --  traverse declarations before references.

   procedure Register_Flow_Scopes (Unit_Node : Node_Id)
   with Pre => Present (Unit_Node);
   --  Creates vertices in the visibility graph

   procedure Connect_Flow_Scopes;
   --  Creates edges in the visibility graph

   function Is_Visible
     (Looking_From : Flow_Scope;
      Looking_At   : Flow_Scope)
      return Boolean;
   --  Returns True iff Looking_From has visibility of Looking_At

   type Hierarchy_Info_T is record
      Is_Package      : Boolean;
      Is_Private      : Boolean;

      Parent          : Entity_Id;
      Instance_Parent : Entity_Id;
      Template        : Entity_Id;
      Container       : Flow_Scope;
   end record;
   --  A minimal description of an entity location within the code hierarchy

   generic
      with procedure Process (E : Entity_Id; Info : Hierarchy_Info_T);
   procedure Iterate_Flow_Scopes
   with Pre => Gnat2Why_Args.Global_Gen_Mode;
   --  Call Process on every registered flow scope
   --  ??? this should be only exposed to serialization, which itself is only
   --  exposed to Flow_Generated_Globals.Phase_1; one day the entire hierarchy
   --  of flow packages should be revisited...

end Flow_Visibility;
