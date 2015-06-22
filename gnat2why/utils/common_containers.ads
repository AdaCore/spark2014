------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                    C O M M O N _ C O N T A I N E R S                     --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--               Copyright (C) 2014-2015, Altran UK Limited                 --
--               Copyright (C) 2014-2015, AdaCore                           --
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
with Ada.Containers.Ordered_Sets;
with Ada.Containers.Vectors;
with Ada.Strings.Unbounded;

with Namet; use Namet;
with Types; use Types;

--  This package contains a few common types (and expression functions)
--  which are used throughout gnat2why (frame conditions, flow and why
--  generation).

package Common_Containers is

   package Node_Lists is new Ada.Containers.Doubly_Linked_Lists (Node_Id);
   --  Standard list of nodes. It is often more convenient to use these,
   --  compared to List_Id in the GNAT frontend, as a Node_Id can be in
   --  any number of these lists, while it can be only in one List_Id.

   package Entity_Vectors is new Ada.Containers.Vectors
     (Index_Type   => Positive,
      Element_Type => Entity_Id);

   function Node_Hash (X : Node_Id) return Ada.Containers.Hash_Type
   is (Ada.Containers.Hash_Type (X));
   --  Compute a hash of a node

   package Node_Sets is new Ada.Containers.Ordered_Sets
     (Element_Type => Node_Id,
      "<"          => "<",
      "="          => "=");
   --  Sets of ordered nodes. We prefer ordered rather than hashed sets, as the
   --  order of iterating over them influence the generation of Why code, which
   --  we intend to be as predictable as possible on all machines, to get the
   --  same proof results on all machines when possible.

   package Node_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Node_Id,
      Element_Type    => Node_Id,
      Hash            => Node_Hash,
      Equivalent_Keys => "=",
      "="             => "=");
   --  Maps of nodes

   package Node_Graphs is new Ada.Containers.Hashed_Maps
     (Key_Type        => Node_Id,
      Element_Type    => Node_Sets.Set,
      Hash            => Node_Hash,
      Equivalent_Keys => "=",
      "="             => Node_Sets."=");
   --  Maps of nodes to sets of nodes

   type Entity_Name is record
      Id : Integer;
      S  : Ada.Strings.Unbounded.String_Access;
   end record;

   function To_Entity_Name (S : String) return Entity_Name;

   function To_Entity_Name (E : Entity_Id) return Entity_Name;

   function To_String (E : Entity_Name) return String;

   function Name_Equal (Left, Right : Entity_Name) return Boolean is
      (Left.Id = Right.Id);

   Null_Entity_Name : constant Entity_Name := Entity_Name'(Id => 0, S => null);

   function Name_Hash (E : Entity_Name) return Ada.Containers.Hash_Type is
      (Ada.Containers.Hash_Type (E.Id));

   package Name_Sets is new Ada.Containers.Hashed_Sets
     (Element_Type        => Entity_Name,
      Hash                => Name_Hash,
      Equivalent_Elements => Name_Equal,
      "="                 => Name_Equal);

   package Name_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Name,
      Element_Type    => Entity_Name,
      Hash            => Name_Hash,
      Equivalent_Keys => Name_Equal,
      "="             => Name_Equal);

   function Name_Id_Hash (N : Name_Id) return Ada.Containers.Hash_Type is
     (Ada.Containers.Hash_Type (N));

end Common_Containers;
