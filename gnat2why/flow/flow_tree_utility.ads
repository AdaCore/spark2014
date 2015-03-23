------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                    F L O W _ T R E E _ U T I L I T Y                     --
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

--  This package contains utilities related to the gnat tree.

with Ada.Containers;

with Atree;             use Atree;
with Einfo;             use Einfo;
with Sinfo;             use Sinfo;
with Types;             use Types;

package Flow_Tree_Utility with
   Initial_Condition => not Is_Initialized
is

   procedure Initialize;
   --  Set up state required by some functions in this package.

   function Is_Initialized return Boolean;
   --  Tests if we're initialized.

   function Component_Hash (E : Entity_Id) return Ada.Containers.Hash_Type
     with Pre => Is_Initialized and then
                 Nkind (E) in N_Entity and then
                 Ekind (E) in E_Component | E_Discriminant;
   --  Compute a suitable hash for the given record component.

   function Same_Component (C1, C2 : Entity_Id) return Boolean
     with Pre => Is_Initialized and then
                 Nkind (C1) in N_Entity and then
                 Nkind (C2) in N_Entity and then
                 Ekind (C1) in E_Component | E_Discriminant  and then
                 Ekind (C2) in E_Component | E_Discriminant;
   --  Given two record components, checks if one can be considered to be
   --  the `same' component (for purposes of flow analysis). For example a
   --  record might contain component x, and its derived record also
   --  contains this component x (but its a different entity). This
   --  function can be used to check for this equivalence.

private
   Init_Done : Boolean := False;

   --------------------
   -- Is_Initialized --
   --------------------

   function Is_Initialized return Boolean is (Init_Done);

end Flow_Tree_Utility;
