------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        C O N S T A N T _ T R E E                         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2014, AdaCore                   --
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
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

generic
   type Node_Type is (<>);
   Root : Node_Type;
package Constant_Tree is
   --  This package provides ways to manipulate constant
   --  trees (e.g. trees of type hierarchy).
   --
   --  The interface of this package depends on its current state.
   --  Its state can be "not frozen" or "frozen"
   --
   --  * not frozen: the tree can only be modified, not queried. At elaboration
   --  time, the tree is "flat": Root is the direct parent of all other node.
   --  To build the tree, one would move children around using Move_Child
   --  to create some depths, then call Freeze when he is done organizing it.
   --
   --  * frozen: the tree cannot be modified anymore, and can be queried.

   function Is_Frozen return Boolean;

   procedure Move_Child (New_Parent : Node_Type; Child : Node_Type)
     with Pre => (not Is_Frozen);
   --  Remove Child from the tree and re-insert it as a child of New_Parent

   procedure Freeze
     with Pre => (not Is_Frozen);
   --  Freeze the package; the tree will then be unmodifiable

   function LCA (Left, Right : Node_Type) return Node_Type
     with Pre => (Is_Frozen);
   --  Return the lowest common ancestor for the given nodes

   function Up (Node : Node_Type) return Node_Type
     with Pre => (Is_Frozen);
   --  If Node is the root node, return it; otherwise,
   --  return this node's father.

   function Up (From, To : Node_Type) return Node_Type
     with Pre => (Is_Frozen);
   --  Same as unary Up, except that it stops when To is reached;
   --  i.e. if From = To then To is returned.

private
   Frozen : Boolean := False;

   function Is_Frozen return Boolean is (Frozen);

end Constant_Tree;
