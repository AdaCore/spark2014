------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                     W H Y - A T R E E - T A B L E S                      --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010, AdaCore                        --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute it and/or modify it   --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. gnat2why is distributed in the hope that it will  be  useful,   --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHAN-  --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Unchecked_Conversion;
with Ada.Containers.Vectors;
with Ada.Containers.Doubly_Linked_Lists;

with Why.Sinfo; use Why.Sinfo;
with Why.Types; use Why.Types;

package Why.Atree.Tables is
   --  This package allows to allocate new Why nodes and to associate
   --  then with an node Id.

   function New_Why_Node_Id (Node : Why_Node) return Why_Node_Id;
   pragma Precondition (Node.Kind /= W_Unused_At_Start);
   pragma Postcondition (Get_Node (New_Why_Node_Id'Result) = Node);
   pragma Inline (New_Why_Node_Id);
   --  Allocate a new Why node in table, and return its Id

   function Get_Node (Node_Id : Why_Node_Id) return Why_Node;
   --  Get the node whose id is Node_Id

   function Get_Kind (Node_Id : Why_Node_Id) return Why_Node_Kind;
   --  Get the kind of Node_Id

   function Option
     (Node  : Why_Node_Id;
      Value : Why_Node_Kind)
     return Boolean;
   --  Return True if Node is Empty or has kind Value

private
   --  These tables are used as storage pools for nodes and lists.
   --  They could ultimately be implemented using the containers
   --  that will be defined in the context of Hi-Lite; for now,
   --  use Standard Ada 05 containers, in the hope that Hi-Lite
   --  containers will be similar enough.

   package Node_Tables is
     new Ada.Containers.Vectors (Index_Type   => Why_Node_Id,
                                 Element_Type => Why_Node,
                                 "=" => "=");

   Node_Table : Node_Tables.Vector;

   package Node_Lists is
     new Ada.Containers.Doubly_Linked_Lists (Element_Type => Why_Node_Id,
                                             "=" => "=");

   function "=" (Left, Right : Node_Lists.List) return Boolean;
   --  Return True if Left and Right have the same extension

   package Node_List_Tables is
     new Ada.Containers.Vectors (Index_Type => Why_Node_List,
                                 Element_Type => Node_Lists.List,
                                 "=" => "=");

   function Get_Node (Node_Id : Why_Node_Id) return Why_Node is
      (Node_Tables.Element (Node_Table, Node_Id));

   function Get_Kind (Node_Id : Why_Node_Id) return Why_Node_Kind is
      (Get_Node (Node_Id).Kind);

   function Option
     (Node  : Why_Node_Id;
      Value : Why_Node_Kind)
     return Boolean is
      (Node = Why_Empty or else Get_Kind (Node) = Value);

end Why.Atree.Tables;
