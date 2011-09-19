------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                             W H Y - I N T E R                            --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
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

with Ada.Containers;                     use Ada.Containers;
with Ada.Containers.Doubly_Linked_Lists;

with Atree;                              use Atree;
with Sinfo;                              use Sinfo;
with String_Utils;                       use String_Utils;
with Types;                              use Types;
pragma Warnings (Off);
--  ??? Why.Sinfo" is directly visible as "Sinfo", as it has "Why" as a
--  common ancestor with the current package. So it hides compilation unit
--  with the same name ("Sinfo"). Maybe we should think of renaming it to
--  "Why.W_Sinfo".
with Why.Sinfo;                          use Why.Sinfo;
pragma Warnings (On);
with Why.Ids;                            use Why.Ids;
with Why.Atree.Builders;                 use Why.Atree.Builders;

package Why.Inter is
   --  This package contains types that are used to represent intermediate
   --  phases of the translation process.

   package List_Of_Nodes is new Doubly_Linked_Lists (Node_Id);
   --  Standard list of nodes. It is better to use these, as a Node_Id can be
   --  in any number of these lists, while it can be only in one List_Id.

   type Why_Package is
      record
         WP_Name           : access String;
         WP_Context        : String_Lists.List;
         WP_Decls          : List_Of_Nodes.List;
         --  All declarations of the package that in Alfa and that are not
         --  types.
         WP_Decls_As_Spec  : List_Of_Nodes.List;
         --  Special list of declarations for subprogram specs *and* subprogram
         --  bodies which are their own spec. A spec should be generated for
         --  these, not a body (which is generated or not somewhere else).
         WP_Types          : List_Of_Nodes.List;
         --  List of type declarations that are in Alfa. They are translated
         --  to Why entirely.
         WP_Abstract_Types : List_Of_Nodes.List;
         --  Special list for types that are not in Alfa, but for which we
         --  still generate abstract type declarations in Why.
         WP_Abstract_Obj : List_Of_Nodes.List;
         --  Special list for objects that are not in Alfa (either because of
         --  their type, or because of their initialization expression), but
         --  for which we still generate a parameter. This parameter may be
         --  used in frame conditions.
      end record;
   --  This type represents a Why package (file), whose list of declarations
   --  is not yet translated. Such a package has a name, a list of packages to
   --  include and the list of Ada nodes yet to be translated.

   package List_Of_Why_Packs is new Doubly_Linked_Lists (Why_Package);

   function Make_Empty_Why_Pack (S : String) return Why_Package;
   --  Build an empty Why_Package with the given name

   procedure Add_With_Clause (P : out Why_Package; Name : String);
   --  Add a package name to the context of a Why package.

   procedure Add_With_Clause (P : out Why_Package; Other : Why_Package);
   --  Add a package name to the context of a Why package.

   EW_Bool_Type : constant W_Base_Type_Id :=
                    New_Base_Type (Base_Type => EW_Bool);
   EW_Int_Type  : constant W_Base_Type_Id :=
                    New_Base_Type (Base_Type => EW_Int);
   EW_Real_Type : constant W_Base_Type_Id :=
                    New_Base_Type (Base_Type => EW_Real);

   type Why_Scalar_Type_Array is array (EW_Scalar) of W_Base_Type_Id;

   Why_Types : constant Why_Scalar_Type_Array :=
                 (EW_Bool => EW_Bool_Type,
                  EW_Int  => EW_Int_Type,
                  EW_Real => EW_Real_Type);

   function EW_Abstract (N : Node_Id) return W_Base_Type_Id;

   function Base_Why_Type (N : Node_Id) return W_Base_Type_Id;
   function Base_Why_Type (W : W_Base_Type_Id) return W_Base_Type_Id;
   --  Return the base type in Why of the given node
   --  (e.g EW_Real_Type for standard__float).

   function Base_Why_Type (Left, Right : W_Base_Type_Id) return W_Base_Type_Id;
   function Base_Why_Type (Left, Right : Node_Id) return W_Base_Type_Id;
   --  Return the most general base type for Left and Right
   --  (e.g. real in Left=int and Right=real).

   function Get_EW_Type (T : W_Primitive_Type_Id) return EW_Type;
   function Get_EW_Type (T : Node_Id) return EW_Type;
   --  Return the EW_Type of the given entity

   function Up (WT : W_Base_Type_Id) return W_Base_Type_Id;
   --  If WT is the highest base type, return WT; otherwise, return the
   --  smallest base type BT such that WT < BT.

   function Up (From, To : W_Base_Type_Id) return W_Base_Type_Id;
   --  Same as unary Up, except that it stops when To is reached;
   --  i.e. if From = To then To is returned.

   function  LCA (Left, Right : W_Base_Type_Id) return W_Base_Type_Id;
   --  Return the lowest common ancestor in base type hierarchy,
   --  i.e. the smallest base type B such that Left <= B and right <= B.

   function Full_Name (N : Entity_Id) return String
      with Pre => (Nkind (N) = N_Defining_Identifier);
   --  Given an N_Defining_Identifier, return its Full Name, as used in Why.

   function Eq (Left, Right : W_Base_Type_Id) return Boolean;
   --  Extensional equality (i.e. returns True if Left and Right are of
   --  the same kind, and have the same Ada Node if this kind is EW_Abstract).

end Why.Inter;
