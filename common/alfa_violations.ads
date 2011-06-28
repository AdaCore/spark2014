------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                        A L F A _ V I O L A T I O N S                     --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
--                                                                          --
-- gnatprove is  free  software;  you can redistribute it and/or modify it  --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. gnatprove is distributed in the hope that it will  be  useful,  --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHAN-  --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- gnatprove is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Containers;             use Ada.Containers;
with Ada.Containers.Hashed_Maps;
with Ada.Strings.Hash;
with Ada.Strings.Unbounded;      use Ada.Strings.Unbounded;

package Alfa_Violations is

   pragma Elaborate_Body;

   type Vkind is (

      --  NYI: Not Yet Implemented
      --  These constructs should be supported in Alfa one day

      NYI_Aggregate,        --  aggregate
      NYI_Arith_Operation,  --  arithmetic operation
      NYI_Array_Subtype,    --  array subtype
      NYI_Attribute,        --  attribute
      NYI_Block_Statement,  --  block declare statement
      NYI_Concatenation,    --  concatenation
      NYI_Conversion,       --  conversion
      NYI_Container,        --  formal containers
      NYI_Discriminant,     --  discriminant record
      NYI_Dispatch,         --  dispatching
      NYI_Expr_With_Action, --  expression with action
      NYI_Float,            --  float
      NYI_Generic,          --  generics
      NYI_Impure_Function,  --  impure functions
      NYI_Logic_Function,   --  logic functions
      NYI_Modular,          --  modular type and subtype
      NYI_Non_Static_Range, --  non static range in type
      NYI_Old_Attribute,    --  'Old attribute
      NYI_Pragma,           --  pragma
      NYI_Qualification,    --  qualification
      NYI_Rep_Clause,       --  representation clause
      NYI_Slice,            --  array slice
      NYI_String_Literal,   --  string literal
      NYI_Tagged,           --  tagged type
      NYI_XXX,              --  all other cases

      --  NIR: Not In Roadmap
      --  These constructs are not in Alfa in the foreseeable future

      NIR_Access,           --  access types
      NIR_Ambiguous_Expr,   --  ambiguous expr
      NIR_Dealloc,          --  deallocation
      NIR_Dynamic_Alloc,    --  dynamic allocation
      NIR_Exception,        --  exception
      NIR_Indirect_Call,    --  indirect call
      NIR_Tasking,          --  tasks and protected objects
      NIR_Unchecked_Conv,   --  unchecked conversion
      NIR_XXX);             --  all other cases

   subtype Not_Yet_Implemented is Vkind range NYI_Aggregate .. NYI_XXX;
   subtype Known_Not_Yet_Implemented is Not_Yet_Implemented range
     Not_Yet_Implemented'First ..
       Not_Yet_Implemented'Val
         (Not_Yet_Implemented'Pos (Not_Yet_Implemented'Last) - 1);
   subtype Not_In_Roadmap is Vkind range NIR_Access .. NIR_XXX;
   subtype Known_Not_In_Roadmap is Not_In_Roadmap range
     Not_In_Roadmap'First ..
       Not_In_Roadmap'Val
         (Not_In_Roadmap'Pos (Not_In_Roadmap'Last) - 1);

   function Is_Not_Yet_Implemented (V : Vkind) return Boolean is
      (V in Not_Yet_Implemented);

   function Is_Not_In_Roadmap (V : Vkind) return Boolean is
      (V in Not_In_Roadmap);

   --  Use only alphanumeric characters and spaces for violation messages,
   --  as this property is used later to read .alfa files

   Violation_Msg : constant array (Vkind) of Unbounded_String :=
     (
      NYI_Aggregate        => To_Unbounded_String ("aggregate"),
      NYI_Arith_Operation  => To_Unbounded_String ("arithmetic operation"),
      NYI_Array_Subtype    => To_Unbounded_String ("array subtype"),
      NYI_Attribute        => To_Unbounded_String ("attribute"),
      NYI_Block_Statement  => To_Unbounded_String ("block statement"),
      NYI_Concatenation    => To_Unbounded_String ("concatenation"),
      NYI_Conversion       => To_Unbounded_String ("conversion"),
      NYI_Container        => To_Unbounded_String ("container"),
      NYI_Discriminant     => To_Unbounded_String ("discriminant"),
      NYI_Dispatch         => To_Unbounded_String ("dispatch"),
      NYI_Expr_With_Action => To_Unbounded_String ("expression with action"),
      NYI_Float            => To_Unbounded_String ("float"),
      NYI_Generic          => To_Unbounded_String ("generic"),
      NYI_Impure_Function  => To_Unbounded_String ("impure function"),
      NYI_Logic_Function   => To_Unbounded_String ("logic function"),
      NYI_Modular          => To_Unbounded_String ("modular"),
      NYI_Non_Static_Range => To_Unbounded_String ("non static range"),
      NYI_Old_Attribute    => To_Unbounded_String ("Old attribute"),
      NYI_Pragma           => To_Unbounded_String ("pragma"),
      NYI_Qualification    => To_Unbounded_String ("qualification"),
      NYI_Rep_Clause       => To_Unbounded_String ("representation clause"),
      NYI_Slice            => To_Unbounded_String ("slice"),
      NYI_String_Literal   => To_Unbounded_String ("string literal"),
      NYI_Tagged           => To_Unbounded_String ("tagged type"),
      NYI_XXX              => To_Unbounded_String ("not yet implemented"),

      NIR_Access           => To_Unbounded_String ("access"),
      NIR_Ambiguous_Expr   => To_Unbounded_String ("ambiguous expr"),
      NIR_Dealloc          => To_Unbounded_String ("deallocation"),
      NIR_Dynamic_Alloc    => To_Unbounded_String ("dynamic allocation"),
      NIR_Exception        => To_Unbounded_String ("exception"),
      NIR_Indirect_Call    => To_Unbounded_String ("indirect call"),
      NIR_Tasking          => To_Unbounded_String ("tasking"),
      NIR_Unchecked_Conv   => To_Unbounded_String ("unchecked conversion"),
      NIR_XXX              => To_Unbounded_String ("unsupported construct"));

   function Name_Equal (Left, Right : Unbounded_String) return Boolean is
      (To_String (Left) = To_String (Right));

   function Name_Hash (N : Unbounded_String) return Hash_Type is
      (Ada.Strings.Hash (To_String (N)));

   package Name_Map is new Hashed_Maps
     (Key_Type        => Unbounded_String,
      Element_Type    => Vkind,
      Hash            => Name_Hash,
      Equivalent_Keys => "=",
      "="             => "=");

   use Name_Map;

   Violation_From_Msg : Map;

end Alfa_Violations;
