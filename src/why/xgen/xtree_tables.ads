------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         X T R E E _ T A B L E S                          --
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

   type String_Access is access String;

   type Field_Kind_Type is
     (Field_Variant,
      --  kind-specific field

      Field_Special,
      --  Special field, updated by internal operations

      Field_Domain,
      --  Domain field, updated by internal operations

      Field_Common
      --  Common field, present for any kind
      );

   type Field_Info is record
      --  Structural information about a field of a node

      Field_Name     : String_Access;
      --  Field name

      Field_Type     : String_Access;
      --  Field type

      Default        : String_Access;
      --  Default field value ("" if none)

      Id_Type        : String_Access;
      --  Checked id subtype, if any

      Field_Kind     : Field_Kind_Type;
      --  Field kind: whether the field is in any node or not,
      --  whether it is special or regular...

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

      Is_Mutable            : Boolean := False;
      --  True if the nodes of this kind can be modified

      Domain                : EW_ODomain := EW_Expr;
      --  Domain of nodes of this kind; EW_Expr if it is not known
      --  a priori.

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
                                     False,
                                     EW_Expr,
                                     Node_Lists.Empty_List);

   ------------------
   -- Variant Part --
   ------------------

   subtype Valid_Kind is Why_Node_Kind
     range W_Type .. Why_Node_Kind'Last;

   Why_Tree_Info : array (Why_Node_Kind) of Why_Node_Info;
   --  Structural info for the variant part of the Why syntax tree

   ----------------
   -- Operations --
   ----------------

   procedure New_Common_Field
     (Field_Name : String;
      Field_Type : String;
      Default    : String := "");

   procedure New_Domain_Field
     (Field_Name : String;
      Field_Type : String;
      Default    : String := "");

   procedure New_Special_Field
     (Field_Name : String;
      Field_Type : String;
      Default    : String := "");

   procedure New_Field
     (Kind       : Why_Node_Kind;
      Field_Name : String;
      Field_Type : String;
      Default    : String := "");

   procedure New_Field
     (Kind         : Why_Node_Kind;
      Field_Name   : String;
      Field_Kind   : String;
      Multiplicity : Id_Multiplicity);

   procedure New_Field
     (NI         : in out Why_Node_Info;
      Field_Kind : Field_Kind_Type;
      Field_Name : String;
      Field_Type : String;
      Default    : String);
   --  Add new field info to the node info

   procedure Set_Mutable (Kind : Why_Node_Kind);
   --  Specify that the nodes of the given node kind are not constant

   function Get_Domain (Kind : Why_Node_Kind) return EW_ODomain;
   procedure Set_Domain (Kind : Why_Node_Kind; Domain : EW_ODomain);
   function Get_Domain (Kind : Why_Node_Kind) return Class_Info;
   --  Accessor/mutator for domains

   function Is_Mutable (Kind : Why_Node_Kind) return Boolean;
   --  Return whether the nodes of the given node kind are mutable

   function Has_Variant_Part (Kind : Why_Node_Kind) return Boolean;
   --  True if a node of this kind has a variant part (i.e. is not
   --  a leaf in the syntax tree; e.g. this returns False for
   --  W_Type_Unit).

   function Param_Name
     (FI : Field_Info)
     return String;
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

   function Accessor_Name
     (Kind : Why_Node_Kind;
      IK   : Id_Kind;
      FI   : Field_Info)
     return String;
   --  Return the accessor name for the given field of the given node kind

   type List_Op_Kind is (Op_Append, Op_Prepend);

   function List_Op_Name
     (List_Op : List_Op_Kind)
     return String;

   function List_Op_Name
     (Kind    : Why_Node_Kind;
      FI      : Field_Info;
      List_Op : List_Op_Kind)
     return String;
   pragma Precondition (Is_List (FI));
   --  Return the name of the append/prepend routine for the given field
   --  of the given node kind

   function Mutator_Name
     (Kind : Why_Node_Kind;
      FI   : Field_Info)
     return String;
   --  Return the mutator name for the given field of the given node kind

   type Builder_Context is (In_Builder_Spec, In_Builder_Body);
   --  Context in which we are emitting a construct. This is mainly use
   --  for lists in builder, where they can be represented either by a
   --  container, or by an array, depending on whether we are emitting the
   --  spec or the implementation.

   function Builder_Name
     (Kind : Why_Node_Kind;
      IK   : Id_Kind := Regular)
     return String;
   --  Return the builder name for the given node kind

   function Builder_Name
     (Prefix : String;
      IK     : Id_Kind := Regular)
     return String;

   function Builder_Param_Type
     (FI      : Field_Info;
      IK      : Id_Kind;
      Context : Builder_Context)
     return String;

   function Has_Default_Value
     (Kind    : Why_Node_Kind;
      FI      : Field_Info;
      IK      : Id_Kind := Regular;
      Context : Builder_Context := In_Builder_Body)
     return Boolean;
   --  Return True if the given field has an appropriate default value

   function Default_Value
     (Kind    : Why_Node_Kind;
      FI      : Field_Info;
      IK      : Id_Kind := Regular;
      Context : Builder_Context := In_Builder_Body)
     return String;
   --  Return a default value for the given field if one exists, "" otherwise

   function Traversal_Pre_Op (Kind : Why_Node_Kind) return String;
   --  Return the name of prep op hooks for a given node kind
   --  in recursive traversals. Prep Op hooks are called before going
   --  recursively through children of a given node.

   function Traversal_Post_Op (Kind : Why_Node_Kind) return String;
   --  Return the name of post op hooks for a given kind
   --  in recursive traversals. Post Op hooks are called after having
   --  gone recursively through children of a given node.

   function Field_Name (FI : Field_Info) return String;
   --  Return the name of this field

   function Node_Kind (FI : Field_Info) return String;
   pragma Precondition (Is_Why_Id (FI));
   --  For a node field, return its node kind

   function Type_Name
     (FI   : Field_Info;
      Kind : Id_Kind)
     return String;
   --  Return the kind-specific id subtype name if FI is a node;
   --  otherwise, return the type of this field (e.g. Name_Id, Uint, Ureal),
   --  ignoring Kind parameter.

   function Element_Type_Name
     (FI   : Field_Info;
      Kind : Id_Kind)
     return String;
   pragma Precondition (Is_List (FI));
   --  Return the id type of elements of FI, assuming that FI is a list

   function List_Type_Name (Kind : Why_Node_Kind) return String;
   --  Return the kind-specific list subtype name

   function Is_List (FI : Field_Info) return Boolean;
   --  True if FI is a subtype of Why_Node_List

   function Maybe_Null (FI : Field_Info) return Boolean;
   --  True if this field may be null or empty

   function Is_Why_Id (FI : Field_Info) return Boolean;
   --  True if the type of this field is a subtype of Why_Node_Id
   --  or a subtype of Why_Node_List.

   function Field_Kind (FI : Field_Info) return Field_Kind_Type;
   --  Return the kind of the field; e.g. whether it is kind-specific
   --  or shared among nodes, or for internal use only...

   function Multiplicity (FI : Field_Info) return Id_Multiplicity;
   pragma Precondition (Is_Why_Id (FI));
   --  For a node child, return corresponding multiplicity

end Xtree_Tables;
