------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                    C O M M O N _ C O N T A I N E R S                     --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                Copyright (C) 2014-2021, Altran UK Limited                --
--                     Copyright (C) 2014-2021, AdaCore                     --
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

with Atree;            use Atree;
with Einfo;            use Einfo;
with GNATCOLL.Symbols; use GNATCOLL.Symbols;
with Hashing;          use Hashing;
with Types;            use Types;
with Checked_Types;    use Checked_Types;

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

   package Hashed_Node_Sets is new Ada.Containers.Hashed_Sets
     (Element_Type        => Node_Id,
      Hash                => Node_Hash,
      Equivalent_Elements => "=");
   --  Set of nodes for use where ordering doesn't matter but performance does

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

   package Node_To_Bool_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Node_Id,
      Element_Type    => Boolean,
      Hash            => Common_Containers.Node_Hash,
      Equivalent_Keys => "=");
   --  Maps of nodes to booleans

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

   function To_Entity_Name (S : String) return Entity_Name
   with Pre => S /= "";

   function To_Entity_Name (E : Entity_Id) return Entity_Name
   with Pre => Ekind (E) not in E_Package_Body
                              | E_Protected_Body
                              | E_Subprogram_Body
                              | E_Task_Body
                              | Generic_Unit_Kind;
   --  Converts Entity_Id to Entity_Name; it should be only called for unique
   --  entities, i.e. not for body entities.

   function To_String (E : Entity_Name) return String
   with Post => To_String'Result /= "";

   package Name_Lists is new Ada.Containers.Doubly_Linked_Lists
     (Element_Type => Entity_Name);

   function Lexical_Less (Left, Right : Entity_Name) return Boolean is
     (To_String (Left) < To_String (Right));
   --  Comparison on Entity_Names; intended for picking the lexically smallest
   --  element from a collection, as hashes might differ across platforms.

   function Name_Hash (E : Entity_Name) return Ada.Containers.Hash_Type is
     (Generic_Integer_Hash (Integer (E)));

   package Name_Sets is new Ada.Containers.Hashed_Sets
     (Element_Type        => Entity_Name,
      Hash                => Name_Hash,
      Equivalent_Elements => "=");

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

   package String_Sets is new Ada.Containers.Indefinite_Hashed_Sets
     (Element_Type        => String,
      Hash                => Ada.Strings.Hash,
      Equivalent_Elements => "=",
      "="                 => "=");

   package Symbol_Sets is new Ada.Containers.Hashed_Sets
     (Element_Type        => Symbol,
      Hash                => GNATCOLL.Symbols.Hash,
      Equivalent_Elements => "=",
      "="                 => "=");

private

   Null_Entity_Name : constant Any_Entity_Name := 0;

end Common_Containers;
