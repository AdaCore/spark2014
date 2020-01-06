------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                     W H Y - A T R E E - T A B L E S                      --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2020, AdaCore                     --
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

with Ada.Containers.Doubly_Linked_Lists;
with Ada.Containers.Indefinite_Vectors;
with Why.Classes;                        use Why.Classes;

package Why.Atree.Tables is
   --  This package allows to allocate new Why nodes and to associate them with
   --  a node Id.

   function New_Why_Node_Id (Node : Why_Node) return Why_Node_Id with
     Pre  => (Node.Kind /= W_Unused_At_Start);
   pragma Inline (New_Why_Node_Id);
   --  Allocate a new Why node in table, and return its Id

   function New_Why_Node_Id (Kind : W_Any_Node) return Why_Node_Id with
     Post => (Get_Kind (New_Why_Node_Id'Result) = Kind);
   pragma Inline (New_Why_Node_Id);
   --  Allocate a new (uninitialized) Why node in table of the given kind

   function Get_Node (Node_Id : Why_Node_Id) return Why_Node;
   --  Get the node whose id is Node_Id

   procedure Set_Node (Node_Id : Why_Node_Id; Node : Why_Node) with
     Post => (Get_Node (Node_Id) = Node);
   --  Assign the given Id to the given Node

   function Get_Link (Node_Id : Why_Node_Id) return Why_Node_Set with Ghost;
   function Get_Link (List_Id : Why_Node_List) return Why_Node_Set with Ghost;

   procedure Set_Link (Node_Id : Why_Node_Id; Link : Why_Node_Set) with
     Post => (Node_Id = Why_Empty
              or else Get_Link (Node_Id) = Link);
   procedure Set_Link (Node_Id : Why_Node_Id; Link : Why_Node_Id) with
     Post => (Node_Id = Why_Empty
              or else Get_Link (Node_Id) = Why_Node_Set (Link));
   procedure Set_Link (Node_Id : Why_Node_Id; Link : Why_Node_List) with
     Post => (Node_Id = Why_Empty
              or else Get_Link (Node_Id) = Why_Node_Set (Link));
   procedure Set_Link (List_Id : Why_Node_List; Link : Why_Node_Set) with
     Post => (Get_Link (List_Id) = Link);
   procedure Set_Link (List_Id : Why_Node_List; Link : Why_Node_Id) with
     Post => (Get_Link (List_Id) = Why_Node_Set (Link));
   procedure Set_Link (List_Id : Why_Node_List; Link : Why_Node_List) with
     Post => (Get_Link (List_Id) = Why_Node_Set (Link));
   --  Set the link of the given node

   procedure Update_Validity_Status
     (Node_Id : Why_Node_Id;
      Checked : Boolean);
   procedure Update_Validity_Status
     (List_Id : Why_Node_List;
      Checked : Boolean);
   --  Set the validity status of the given node/list to the value of Checked

   function Get_Kind (Node_Id : Why_Node_Id) return Why_Node_Kind;
   --  Get the kind of Node_Id

   function Is_Checked (Node_Id : Why_Node_Id) return Boolean;

   package Why_Node_Lists is
     new Ada.Containers.Doubly_Linked_Lists (Element_Type => Why_Node_Id);

   function Get_List (List_Id : Why_Node_List) return Why_Node_Lists.List;

   procedure Append (List_Id : Why_Node_List; New_Item : Why_Node_Id);

   procedure Prepend (List_Id : Why_Node_List; New_Item : Why_Node_Id);

   function Is_Empty (List_Id : Why_Node_List) return Boolean;

   function Is_Checked (List_Id : Why_Node_List) return Boolean;

   function New_List return Why_Node_List with
     Post => (Is_Empty (New_List'Result));
   --  Allocate a new empty list in table and return its Id

   procedure Free;
   --  Free memory allocated for the Why3 AST tables; should only be called
   --  after printing to .mlw file.

private
   --  These tables are used as storage pools for nodes and lists.
   --  They could ultimately be implemented using the containers
   --  that will be defined in the context of SPARK 2014; for now,
   --  use Standard Ada 05 containers, in the hope that SPARK 2014
   --  containers will be similar enough.

   package Node_Tables is
     new Ada.Containers.Indefinite_Vectors (Index_Type   => Why_Node_Id,
                                            Element_Type => Why_Node);

   Node_Table : Node_Tables.Vector;

   type List_Info is record
      Checked : Boolean;
      Link    : Why_Node_Set;
      Content : Why_Node_Lists.List;
   end record;

   package Node_List_Tables is
     new Ada.Containers.Indefinite_Vectors (Index_Type   => Why_Node_List,
                                            Element_Type => List_Info);

   List_Table : Node_List_Tables.Vector;

   function Get_Node (Node_Id : Why_Node_Id) return Why_Node renames
     Node_Table.Element;

   function Get_Kind (Node_Id : Why_Node_Id) return Why_Node_Kind is
     (Node_Table (Node_Id).Kind);

   function Is_Checked (Node_Id : Why_Node_Id) return Boolean is
     (Node_Table (Node_Id).Checked);

   function Get_Link (Node_Id : Why_Node_Id) return Why_Node_Set is
     (Node_Table (Node_Id).Link);

   function Get_Link (List_Id : Why_Node_List) return Why_Node_Set is
     (List_Table (List_Id).Link);

   function Get_List (List_Id : Why_Node_List) return Why_Node_Lists.List is
     (List_Table (List_Id).Content);

   function Is_Empty (List_Id : Why_Node_List) return Boolean is
     (List_Table (List_Id).Content.Is_Empty);

   function Is_Checked (List_Id : Why_Node_List) return Boolean is
     (List_Table (List_Id).Checked);

end Why.Atree.Tables;
