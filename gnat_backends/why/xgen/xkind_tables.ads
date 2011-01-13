------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         X K I N D _ T A B L E S                          --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
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

with Ada.Containers.Doubly_Linked_Lists;

with Why.Sinfo; use Why.Sinfo;

package Xkind_Tables is
   --  This package provides an interface to record information about
   --  kinds and classes of nodes in the Why syntax tree.

   type Wide_String_Access is access Wide_String;

   package String_Lists is
     new Ada.Containers.Doubly_Linked_Lists (Wide_String_Access, "=");

   Kinds   : String_Lists.List;
   --  List of node kinds; extracted from the syntax tree of Why.Sinfo
   --  by the ASIS traversal.

   type Class_Info is record
      Name  : Wide_String_Access;
      First : Wide_String_Access;
      Last  : Wide_String_Access;
   end record;

   package Class_Lists is
     new Ada.Containers.Doubly_Linked_Lists (Class_Info, "=");

   Classes : Class_Lists.List;
   --  List of node classes; extracted from the syntax tree of Why.Sinfo
   --  by the ASIS traversal.

   type Id_Kind is (Opaque, Unchecked, Regular);
   --  Three sort of Ids, as documented in Why.Ids

   type Id_Multiplicity is (Id_One, Id_Lone, Id_Some, Id_Set);
   --  Four multiplicity for Id subtype that matches as follows:
   --  * Id_One  is "Id",    representing exactly one node;
   --  * Id_Lone is "OId",   representing either zero (empty) or one node;
   --  * Id_Some is "List",  representing at least one node;
   --  * Id_Set  is "OList", representing any number of nodes.

   function Multiplicity_Suffix
     (Multiplicity : Id_Multiplicity)
     return Wide_String;
   --  Return the string suffix that corresponds to the given multiplicity

   function Id_Subtype
     (Prefix       : Wide_String;
      Kind         : Id_Kind;
      Multiplicity : Id_Multiplicity)
     return Wide_String;
   --  Return the subtype for the given Kind and the given Multiplicity.
   --  e.g. Id_Subtype ("W_Type", Opaque, Lone) would return
   --  "W_Type_Opaque_OId".

   function Arr_Type (Prefix : Wide_String) return Wide_String;
   --  Return the name of an array type for the elements of the given Prefix
   --  (e.g. of type W_Type_Id is Prefix is "W_Type").

   function Base_Id_Subtype
     (Prefix       : Wide_String;
      Kind         : Id_Kind;
      Multiplicity : Id_Multiplicity)
     return Wide_String;
   --  Same as Id_Subtype, but returning the base subtype: i.e. Why_Node_Id
   --  for Opaque Ids, Opaque Ids for Unchecked Ids, Unchecked Ids for
   --  Regular Ids.

   function Kind_Check
     (Prefix : Wide_String;
      M      : Id_Multiplicity)
     return Wide_String;
   --  Return the name of the kind-validity check for the given
   --  node kind

   function Tree_Check
     (Prefix : Wide_String;
      M      : Id_Multiplicity)
     return Wide_String;
   --  Return the name of the tree-validity check for the given
   --  node kind

   function Children_Check
     (Prefix : Wide_String;
      M      : Id_Multiplicity)
     return Wide_String;
   --  Return the name of the tree-validity check for the children of node
   --  whose kind is given in parameters

   function Cache_Check (M : Id_Multiplicity) return Wide_String;
   --  Return the name of the cached tree-validity check for the given
   --  multiplicity

   function Class_Name (CI : Class_Info) return Wide_String;

   function Class_First (CI : Class_Info) return Why_Node_Kind;
   --  Given the string representation of a node class, return
   --  <this class>'First

   function Class_Last (CI : Class_Info) return Why_Node_Kind;
   --  Given the string representation of a node class, return
   --  <this class>'Last

end Xkind_Tables;
