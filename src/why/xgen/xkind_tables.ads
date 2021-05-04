------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         X K I N D _ T A B L E S                          --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2021, AdaCore                     --
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

with Why.Sinfo; use Why.Sinfo;

package Xkind_Tables is
   --  This package provides an interface to record information about
   --  kinds and classes of nodes in the Why syntax tree.

   type String_Access is access String;

   package String_Lists is
     new Ada.Containers.Doubly_Linked_Lists (String_Access, "=");

   Kinds : String_Lists.List;
   --  List of node kinds; extracted from the syntax tree of Why.Sinfo
   --  by the ASIS traversal.

   type Class_Info is record
      Name   : String_Access;
      Father : String_Access;
      First  : String_Access;
      Last   : String_Access;
   end record;

   package Class_Lists is
     new Ada.Containers.Doubly_Linked_Lists (Class_Info, "=");

   Classes : Class_Lists.List;
   --  List of node classes

   type Id_Kind is (Opaque, Unchecked, Regular, Derived);
   --  Three sort of Ids, as documented in Why.Ids... + Derived.
   --  ??? Derived is a derived type of Why_Node_Id, not a subtype;
   --  this is an experiment to check if we would possible/easy to
   --  use derived types and (generated) conversions instead of subtypes.
   --  If it is indeed easy to use, then it would allow us to check at
   --  compile time an accidental use of a wrong node kind. If so,
   --  Derived would replace Regular at some point. And some more cleanup
   --  may follow.

   type Id_Multiplicity is (Id_Lone, Id_Set, Id_One, Id_Some);
   --  Four multiplicity for Id subtype that matches as follows:
   --  * Id_One  is "Id",    representing exactly one node;
   --  * Id_Lone is "OId",   representing either zero (empty) or one node;
   --  * Id_Some is "List",  representing at least one node;
   --  * Id_Set  is "OList", representing any number of nodes.

   procedure Register_Kinds;

   procedure Init_Domains;

   procedure Display_Domains;

   procedure New_Class
     (Name  : String;
      First : Why_Node_Kind;
      Last  : Why_Node_Kind);

   procedure New_Domain
     (Name   : String;
      Father : String;
      First  : Why_Node_Kind;
      Last   : Why_Node_Kind);

   function Mixed_Case_Name (Kind : Why_Node_Kind) return String;
   function Mixed_Case_Name (M : Id_Multiplicity) return String;
   function Mixed_Case_Name (D : EW_ODomain) return String;
   --  Return the mixed case name of the given node kind

   function Default_Kind return Why_Node_Kind;
   function Default_Kind return String;

   function Multiplicity_Suffix
     (Multiplicity : Id_Multiplicity)
     return String;
   --  Return the string suffix that corresponds to the given multiplicity

   function Id_Subtype
     (Prefix       : String;
      Kind         : Id_Kind := Regular;
      Multiplicity : Id_Multiplicity := Id_One)
     return String;
   --  Return the subtype for the given Kind and the given Multiplicity.
   --  e.g. Id_Subtype ("W_Type", Opaque, Lone) would return
   --  "W_Type_Opaque_OId".

   function Id_Subtype
     (N_Kind       : Why_Node_Kind;
      I_Kind       : Id_Kind := Regular;
      Multiplicity : Id_Multiplicity := Id_One)
     return String;
   --  Ditto

   function Arr_Type (Prefix : String; Kind : Id_Kind) return String
     with Pre => (Kind in Regular .. Derived);
   --  Return the name of an array type for the elements of the given Prefix
   --  (e.g. of type W_Type_Id is Prefix is "W_Type").

   function Base_Id_Subtype
     (Prefix       : String;
      Kind         : Id_Kind;
      Multiplicity : Id_Multiplicity)
     return String;
   --  Same as Id_Subtype, but returning the base subtype: i.e. Why_Node_Id
   --  for Opaque Ids, Opaque Ids for Unchecked Ids, Unchecked Ids for
   --  Regular Ids.

   function Kind_Check
     (Prefix : String;
      M      : Id_Multiplicity)
     return String;
   --  Return the name of the kind-validity check for the given
   --  node kind

   function Tree_Check
     (Prefix : String;
      M      : Id_Multiplicity)
     return String;
   --  Return the name of the tree-validity check for the given
   --  node kind

   function Children_Check
     (Prefix : String;
      M      : Id_Multiplicity)
     return String;
   --  Return the name of the tree-validity check for the children of node
   --  whose kind is given in parameters

   function Cache_Check (M : Id_Multiplicity) return String;
   --  Return the name of the cached tree-validity check for the given
   --  multiplicity

   function Class_Name (CI : Class_Info) return String;

   function Class_First (CI : Class_Info) return Why_Node_Kind;
   --  Given the string representation of a node class, return
   --  <this class>'First

   function Class_Last (CI : Class_Info) return Why_Node_Kind;
   --  Given the string representation of a node class, return
   --  <this class>'Last

   function Is_Domain (CI : Class_Info) return Boolean;

   function Is_Subclass (Inner, Outer : Class_Info) return Boolean;
   --  Return True in Inner is a strict subclass of Outer

   function Is_Domain (Id_Type : String) return Boolean;
   --  Return True if Id_Type is in a domain class (e.g. W_Term_Id
   --  is in the domain class W_Term, that corresponds to the domain EW_Term).

   function Get_Domain (Id_Type : String) return EW_ODomain;
   --  Return the domain of Id_Type

end Xkind_Tables;
