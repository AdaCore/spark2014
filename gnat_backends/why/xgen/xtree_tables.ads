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
with Why.Sinfo; use Why.Sinfo;

package Xtree_Tables is
   --  This package provide an interface to record structural information
   --  about Why syntax trees.

   type String_Access is access Wide_String;

   type Field_Info is record
      --  Structural information about a field of a node

      Field_Name     : String_Access;
      --  Field name

      Field_Type     : String_Access;
      --  Field type

      Is_Why_Node_Id : Boolean;
      --  Whether or not the type of this field is a subtype of Why_Node_Id
      --  ??? Not used yet; always set to False for now.

      Is_List        : Boolean;
      --  Whether or not the type of this field is a subtype of Why_Node_List
      --  ??? Not used yet; always set to False for now.

      Maybe_Null     : Boolean;
      --  Whether or not this field is optional for its node
      --  (i.e. if it can be Empty).
      --  ??? Not used yet; always set to False for now.
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

   Common_Fields : Why_Node_Info := (0,
                                     Why_Node_Kind'First,
                                     Why_Node_Kind'Last,
                                     Node_Lists.Empty_List);
   --  Fields that are shared amongst all node kinds

   Why_Tree_Info : array (Why_Node_Kind) of Why_Node_Info;
   --  Structural info for the variant part of the Why syntax tree

   procedure New_Field (NI : in out Why_Node_Info; FI : Field_Info);
   --  Add new field info to the node info

   function Param_Name (Field_Name : Wide_String) return Wide_String;
   --  Given a Field_Name, return the name to be use for the corresponding
   --  parameter (in, say, a builder or an accessor). This is meant to be
   --  used to have proper indentation of these parameters.

   function Max_Param_Length (Kind : Why_Node_Kind) return Natural;
   --  Return the maximum length of a parameter for the given node kind

   function Mixed_Case_Name (Kind : Why_Node_Kind) return Wide_String;
   --  Return the mixed case name of the given node kind

   function Builder_Name (Kind : Why_Node_Kind) return Wide_String;
   --  Return the builder name for the given node kind

   function Id_Type_Name (Kind : Why_Node_Kind) return Wide_String;
   --  Return the kind-specific id subtype name

   function List_Type_Name (Kind : Why_Node_Kind) return Wide_String;
   --  Return the kind-specific list subtype name

end Xtree_Tables;
