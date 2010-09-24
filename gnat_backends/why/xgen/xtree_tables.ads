------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         X T R E E _ T A B L E S                          --
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

with Ada.Containers.Doubly_Linked_Lists;
with Why.Sinfo;    use Why.Sinfo;
with Xkind_Tables; use Xkind_Tables;

package Xtree_Tables is
   --  This package provide an interface to record structural information
   --  about Why syntax trees.

   ----------------------
   -- Node description --
   ----------------------

   --  Types that are used to describe syntax nodes and their
   --  corresponding fields (common, special or in variant part).

   type String_Access is access Wide_String;

   type Field_Info is record
      --  Structural information about a field of a node

      Field_Name     : String_Access;
      --  Field name

      Field_Type     : String_Access;
      --  Field type

      Id_Type        : String_Access;
      --  Checked id subtype, if any

      In_Variant     : Boolean;
      --  False if this field is shared amongst all kinds, True if
      --  it is kind-specific.

      Is_Why_Id      : Boolean;
      --  Whether or not the type of this field is a subtype of Why_Node_Id
      --  or a subtype of Why_Node_List.

      Is_List        : Boolean;
      --  Whether or not the type of this field is a subtype of Why_Node_List

      Maybe_Null     : Boolean;
      --  Whether or not this field is optional for its node
      --  (i.e. if it can be Empty).
   end record;

   package Node_Lists is
      new Ada.Containers.Doubly_Linked_Lists (Element_Type => Field_Info,
                                              "=" => "=");

   type Why_Node_Info is record
      --  Structural information about a node in Why syntax trees

      Max_Field_Name_Length : Natural := 0;
      --  Max length of the field names; to be used for pretty indentation

      Variant_Range_First   : Why_Node_Kind;
      --  In the variant part, several fields may be shared amongst a range
      --  of kinds; this record the first value of this range

      Variant_Range_Last    : Why_Node_Kind;
      --  Same as Variant_Range_First, but for the last value of the range

      Fields                : Node_Lists.List;
      --  List of structural information for fields
   end record;

   -------------------
   -- Common Fields --
   -------------------

   --  Fields that are shared amongst all node kinds

   Common_Fields : Why_Node_Info := (0,
                                     Why_Node_Kind'First,
                                     Why_Node_Kind'Last,
                                     Node_Lists.Empty_List);
   --------------------
   -- Special Fields --
   --------------------

   Special_Field_Prefix : constant Wide_String := "Special_Field_";
   --  String representation of the common prefix of each
   --  enum literal in Special_Field_Kind.

   type Special_Field_Kind is
     (Special_Field_None,
      Special_Field_Link,
      Special_Field_Checked);
   --  Lists all special fields. Each literal shall be a
   --  concatenation of "Special_Field_" with the name of
   --  the special field in the node record (e.g. Checked).
   --  The first field (Special_Field_None) is an exception here:
   --  It does not represent any valid field in the node record,
   --  but is used to represent a "no match" response in lookups.

   subtype Valid_Special_Field_Kind is Special_Field_Kind range
     Special_Field_Kind'Succ (Special_Field_Kind'First)
     .. Special_Field_Kind'Last;

   Special_Fields : array (Valid_Special_Field_Kind) of Field_Info;

   function To_String (Kind : Special_Field_Kind) return Wide_String;
   --  Name of the special field in the node record

   function To_Special_Field_Kind
     (Name : Wide_String)
     return Special_Field_Kind;
   --  Given a field name, return the corresponding special field kind;
   --  and Special_Field_None is there is no corresponding special field
   --  kind.

   ------------------
   -- Variant Part --
   ------------------

   subtype Valid_Kind is Why_Node_Kind
     range W_Identifier .. Why_Node_Kind'Last;

   Why_Tree_Info : array (Why_Node_Kind) of Why_Node_Info;
   --  Structural info for the variant part of the Why syntax tree

   ----------------
   -- Operations --
   ----------------

   procedure New_Field
     (NI         : in out Why_Node_Info;
      In_Variant : Boolean;
      Field_Name : Wide_String;
      Field_Type : Wide_String);
   --  Add new field info to the node info

   function Has_Variant_Part (Kind : Why_Node_Kind) return Boolean;
   --  True if a node of this kind has a variant part (i.e. is not
   --  a leaf in the syntax tree; e.g. this returns False for
   --  W_Type_Unit).

   function Param_Name
     (FI : Field_Info)
     return Wide_String;
   --  Given a field info, return the name to be use for the corresponding
   --  parameter (in, say, a builder or an accessor).

   function Max_Field_Name_Length (Kind : Why_Node_Kind) return Natural;
   --  Return the maximum field length for the given node kind;
   --  this is meant to be used to have proper indentation of these parameters.

   function Max_Param_Length
     (Kind                  : Why_Node_Kind;
      Common_Field_Included : Boolean := True)
     return Natural;
   --  Return the maximum length of a parameter for the given node kind;
   --  this is meant to be used to have proper indentation of these parameters.

   function Mixed_Case_Name (Kind : Why_Node_Kind) return Wide_String;
   --  Return the mixed case name of the given node kind

   function Accessor_Name
     (Kind : Why_Node_Kind;
      FI   : Field_Info)
     return Wide_String;
   --  Return the accessor name for the given field of the given node kind

   type List_Op_Kind is (Op_Append, Op_Prepend);

   function List_Op_Name
     (List_Op : List_Op_Kind)
     return Wide_String;

   function List_Op_Name
     (Kind    : Why_Node_Kind;
      FI      : Field_Info;
      List_Op : List_Op_Kind)
     return Wide_String;
   pragma Precondition (Is_List (FI));
   --  Return the name of the append/prepend routine for the given field
   --  of the given node kind

   function Mutator_Name
     (Kind : Why_Node_Kind;
      FI   : Field_Info)
     return Wide_String;
   --  Return the mutator name for the given field of the given node kind

   type Builder_Kind is (Builder_Regular, Builder_Unchecked, Builder_Copy);
   --  Type of builder. Builder_Regular for building builders
   --  that return regular ids (to valid nodes); Builder_Unchecked
   --  for builders that returns unchecked ids (to kind-valid nodes).
   --  Builder_Copy for builders that duplicate the subtree given in
   --  parameter.

   function Builder_Name
     (Kind : Why_Node_Kind;
      BK   : Builder_Kind := Builder_Regular)
     return Wide_String;
   --  Return the builder name for the given node kind

   function Builder_Name
     (Prefix : Wide_String;
      BK     : Builder_Kind := Builder_Regular)
     return Wide_String;

   function Has_Default_Value
     (FI : Field_Info;
      BK : Builder_Kind := Builder_Regular)
     return Boolean;
   --  Return True if the given field has an appropriate default value

   function Default_Value
     (FI : Field_Info;
      BK : Builder_Kind := Builder_Regular)
     return Wide_String;
   --  Return a default value for the given field if one exists, "" otherwise

   function Traversal_Pre_Op (Kind : Why_Node_Kind) return Wide_String;
   --  Return the name of prep op hooks for a given node kind
   --  in recursive traversals. Prep Op hooks are called before going
   --  recursively through children of a given node.

   function Traversal_Post_Op (Kind : Why_Node_Kind) return Wide_String;
   --  Return the name of post op hooks for a given kind
   --  in recursive traversals. Post Op hooks are called after having
   --  gone recursively through children of a given node.

   function Field_Name (FI : Field_Info) return Wide_String;
   --  Return the name of this field

   function Field_Kind (FI : Field_Info) return Wide_String;
   pragma Precondition (Is_Why_Id (FI));
   --  For a node field, return its kind

   function Id_Type_Name (Prefix : Wide_String) return Wide_String;
   function Id_Type_Name (Kind : Why_Node_Kind) return Wide_String;
   function Id_Type_Name (FI : Field_Info) return Wide_String;
   function Unchecked_Id_Type_Name (Kind : Why_Node_Kind) return Wide_String;
   function Unchecked_Id_Type_Name (FI : Field_Info) return Wide_String;
   --  Return the kind-specific id subtype name

   function Unchecked_Element_Type_Name (FI : Field_Info) return Wide_String;
   pragma Precondition (Is_List (FI));

   function List_Type_Name (Kind : Why_Node_Kind) return Wide_String;
   --  Return the kind-specific list subtype name

   function Is_List (FI : Field_Info) return Boolean;
   --  True if FI is a subtype of Why_Node_List

   function In_Variant (FI : Field_Info) return Boolean;
   --  True if this field has been defined in a variant part

   function Maybe_Null (FI : Field_Info) return Boolean;
   --  True if this field may be null or empty

   function Is_Why_Id  (FI : Field_Info) return Boolean;
   --  True if the type of this field is a subtype of Why_Node_Id
   --  or a subtype of Why_Node_List.

   function Multiplicity (FI : Field_Info) return Id_Multiplicity;
   pragma Precondition (Is_Why_Id (FI));
   --  For a node child, return corresponding multiplicity

end Xtree_Tables;
