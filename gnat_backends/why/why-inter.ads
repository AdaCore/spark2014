------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                             W H Y - I N T E R                            --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2012, AdaCore                   --
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
with Ada.Containers.Hashed_Sets;

with Alfa.Frame_Conditions;              use Alfa.Frame_Conditions;

with Atree;                              use Atree;
with Sinfo;                              use Sinfo;
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
with Why.Types;                          use Why.Types;

package Why.Inter is
   --  This package contains types that are used to represent intermediate
   --  phases of the translation process.

   package List_Of_Nodes is new Doubly_Linked_Lists (Node_Id);
   --  Standard list of nodes. It is better to use these, as a Node_Id can be
   --  in any number of these lists, while it can be only in one List_Id.

   function Node_Hash (X : Node_Id) return Hash_Type is (Hash_Type (X));

   package Node_Sets is new Hashed_Sets (Element_Type        => Node_Id,
                                         Hash                => Node_Hash,
                                         Equivalent_Elements => "=",
                                         "="                 => "=");

   type Why_File is
      record
         Name        : access String;
         File        : W_File_Id;
         Cur_Theory  : W_Theory_Declaration_Id;
      end record;

   type Why_File_Enum is
     (WF_Types_In_Spec,
      WF_Types_In_Body,
      WF_Variables,
      WF_Context_In_Spec,
      WF_Context_In_Body,
      WF_Main);

   Why_Files : array (Why_File_Enum) of Why_File;

   function Why_File_Suffix (Kind : Why_File_Enum) return String;

   Standard_Why_Package_Name : constant String := "_standard";

   procedure Init_Why_Files (Prefix : String);
   --  Call this procedure to initialize the predefined Why_Files

   function Make_Empty_Why_File (S : String) return Why_File
     with Post => (Make_Empty_Why_File'Result.Cur_Theory = Why_Empty);
   --  Build an empty Why_File with the given name.

   procedure Close_Theory (P             : in out Why_File;
                           No_Imports    : Boolean := False;
                           Filter_Entity : Entity_Id := Empty)
     with Pre => (P.Cur_Theory /= Why_Empty),
          Post => (P.Cur_Theory = Why_Empty);
   --  Close the current theory by adding all necessary imports and adding the
   --  theory to the file
   --  Skip computing imports when No_Imports is set.

   procedure Open_Theory (P    : in out Why_File;
                          Name : String;
                          Kind : EW_Theory_Type := EW_Module)
     with Pre => (P.Cur_Theory = Why_Empty);
   --  Open a new theory in the file.

   procedure Add_With_Clause (P        : in out Why_File;
                              File     : String;
                              T_Name   : String;
                              Use_Kind : EW_Clone_Type := EW_Import);
   --  Add a package name to the context of a Why package.

   procedure Add_With_Clause (P        : in out Why_File;
                              Other    : Why_File;
                              Use_Kind : EW_Clone_Type := EW_Import);
   --  Add a package name to the context of a Why package.

   procedure Add_Effect_Imports (P : in out Why_File;
                                 S : Name_Set.Set);

   procedure Add_Effect_Imports (T : W_Theory_Declaration_Id;
                                 S : Name_Set.Set);
   --  Add all import clauses that are necessary for the given set of variables

   function Dispatch_Entity (E : Entity_Id) return Why_File_Enum;
   --  Given an Ada Entity, return the appropriate Why File to insert the
   --  entity

   EW_Bool_Type : constant W_Base_Type_Id :=
                    New_Base_Type (Base_Type => EW_Bool);
   EW_Int_Type  : constant W_Base_Type_Id :=
                    New_Base_Type (Base_Type => EW_Int);
   EW_Real_Type : constant W_Base_Type_Id :=
                    New_Base_Type (Base_Type => EW_Real);
   --  This corresponds to a polymorphic type in reality, used only for
   --  conversions in gnat2why.
   EW_Array_Type : constant W_Base_Type_Id :=
                     New_Base_Type (Base_Type => EW_Array);

   type Why_Scalar_Or_Array_Type_Array is
     array (EW_Scalar_Or_Array) of W_Base_Type_Id;

   Why_Types : constant Why_Scalar_Or_Array_Type_Array :=
                 (EW_Bool  => EW_Bool_Type,
                  EW_Int   => EW_Int_Type,
                  EW_Real  => EW_Real_Type,
                  EW_Array => EW_Array_Type);

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
      with Pre => (Nkind (N) in N_Entity);
   --  Given an N_Entity, return its Full Name, as used in Why.

   function Eq (Left, Right : W_Base_Type_Id) return Boolean;
   --  Extensional equality (i.e. returns True if Left and Right are of
   --  the same kind, and have the same Ada Node if this kind is EW_Abstract).

   function Eq (Left, Right : Entity_Id) return Boolean;
   --  Return True if Left and Right corresponds to the same Why identifier

end Why.Inter;
