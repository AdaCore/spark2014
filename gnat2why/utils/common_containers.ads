------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                    C O M M O N _ C O N T A I N E R S                     --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--               Copyright (C) 2014-2016, Altran UK Limited                 --
--               Copyright (C) 2014-2016, AdaCore                           --
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

with Ada.Containers;
with Ada.Containers.Doubly_Linked_Lists;
with Ada.Containers.Hashed_Maps;
with Ada.Containers.Hashed_Sets;
with Ada.Containers.Indefinite_Hashed_Sets;
with Ada.Containers.Ordered_Sets;
with Ada.Containers.Vectors;
with Ada.Strings.Hash;

with Atree;         use Atree;
with Einfo;         use Einfo;
with Hashing;       use Hashing;
with Namet;         use Namet;
with Types;         use Types;

with Checked_Types; use Checked_Types;

--  This package contains a few common types (and expression functions) which
--  are used throughout gnat2why (frame conditions, flow and why generation).

package Common_Containers is

   package Node_Lists is new Ada.Containers.Doubly_Linked_Lists (Node_Id);
   --  Standard list of nodes. It is often more convenient to use these,
   --  compared to List_Id in the GNAT frontend, as a Node_Id can be in
   --  any number of these lists, while it can be only in one List_Id.

   package Entity_Lists is new
     Ada.Containers.Doubly_Linked_Lists (Checked_Entity_Id);

   package Entity_Vectors is new Ada.Containers.Vectors
     (Index_Type   => Positive,
      Element_Type => Checked_Entity_Id);

   function Node_Hash (X : Node_Id) return Ada.Containers.Hash_Type
   is (Generic_Integer_Hash (Integer (X)));
   --  Compute a hash of a node

   package Node_Sets is new Ada.Containers.Ordered_Sets
     (Element_Type => Node_Id);
   --  Sets of ordered nodes. We prefer ordered rather than hashed sets, as the
   --  order of iterating over them influence the generation of Why code, which
   --  we intend to be as predictable as possible on all machines, to get the
   --  same proof results on all machines when possible.

   package Entity_Sets is new Ada.Containers.Ordered_Sets
     (Element_Type => Checked_Entity_Id);

   package Node_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Node_Id,
      Element_Type    => Node_Id,
      Hash            => Node_Hash,
      Equivalent_Keys => "=");
   --  Maps of nodes

   package Node_Graphs is new Ada.Containers.Hashed_Maps
     (Key_Type        => Node_Id,
      Element_Type    => Node_Sets.Set,
      Hash            => Node_Hash,
      Equivalent_Keys => "=",
      "="             => Node_Sets."=");
   --  Maps of nodes to sets of nodes

   type Any_Entity_Name is new Integer range 0 .. Integer'Last;
   --  Entities represented by their string names, which is the only way to
   --  represent entities coming from the bodies of other compilation units
   --  (they get into scope of the analysis when reading the ALI files).
   --
   --  Note: names Any_Entity_Name and Entity_Name below are inspired by
   --  System.Any_Priority and System.Priority.

   Null_Entity_Name : constant Any_Entity_Name;
   --  A special value to represent that no entity is present

   subtype Entity_Name is Any_Entity_Name range 1 .. Any_Entity_Name'Last;
   --  A type that represent non-empty values of entity names

   function To_Entity_Name (S : String) return Entity_Name;

   function To_Entity_Name (E : Entity_Id) return Entity_Name
     with Pre => Ekind (E) not in E_Package_Body    |
                                  E_Protected_Body  |
                                  E_Subprogram_Body |
                                  E_Task_Body;

   function To_String (E : Entity_Name) return String;

   package Name_Lists is new Ada.Containers.Doubly_Linked_Lists
     (Element_Type => Entity_Name);

   function Name_Hash (E : Entity_Name) return Ada.Containers.Hash_Type is
     (Generic_Integer_Hash (Integer (E)));

   package Name_Sets is new Ada.Containers.Hashed_Sets
     (Element_Type        => Entity_Name,
      Hash                => Name_Hash,
      Equivalent_Elements => "=");

   procedure pnames (S : Name_Sets.Set);
   pragma Export (Ada, pnames);
   --  Print set of nodes; for use in gdb

   package Name_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Name,
      Element_Type    => Entity_Name,
      Hash            => Name_Hash,
      Equivalent_Keys => "=");

   package Name_Graphs is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Name,
      Element_Type    => Name_Sets.Set,
      Hash            => Name_Hash,
      Equivalent_Keys => "=",
      "="             => Name_Sets."=");

   function Name_Id_Hash (N : Name_Id) return Ada.Containers.Hash_Type
   is (Generic_Integer_Hash (Integer (N)));

   package Name_Id_Sets is new Ada.Containers.Ordered_Sets
     (Element_Type => Name_Id);

   package String_Sets is new Ada.Containers.Indefinite_Hashed_Sets
     (Element_Type        => String,
      Hash                => Ada.Strings.Hash,
      Equivalent_Elements => "=",
      "="                 => "=");

   function To_Name_Set (S : Node_Sets.Set) return Name_Sets.Set;
   --  Takes a set of Node_Ids and returns a set of Entity_Names

private

   Null_Entity_Name : constant Any_Entity_Name := 0;

end Common_Containers;
