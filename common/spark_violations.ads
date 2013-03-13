------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                       S P A R K _ V I O L A T I O N S                    --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2013, AdaCore                   --
--                                                                          --
-- gnatprove is  free  software;  you can redistribute it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnatprove is distributed  in the hope that  it will be useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General Public License  distributed with  gnatprove;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnatprove is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Containers;             use Ada.Containers;
with Ada.Containers.Hashed_Maps;
with Ada.Strings.Hash;
with Ada.Strings.Unbounded;      use Ada.Strings.Unbounded;

package SPARK_Violations is

   pragma Elaborate_Body;

   type Vkind is (

      --  NYI: Not Yet Implemented
      --  These constructs should be supported in SPARK one day

      NYI_Aggregate,        --  aggregate
      NYI_Arith_Operation,  --  arithmetic operation
      NYI_Attribute,        --  attribute
      NYI_Concatenation,    --  concatenation
      NYI_Container,        --  formal containers
      NYI_Dispatch,         --  dispatching
      NYI_Expr_With_Action, --  expression with action
      NYI_Invariant,        --  type invariant
      NYI_Multi_Dim_Array,  --  multi-dimensional array of dimention > 2
      NYI_Pragma,           --  pragma
      NYI_Predicate,        --  type predicate
      NYI_Rep_Clause,       --  representation clause
      NYI_Tagged,           --  tagged type
      NYI_Array_Operation,  --  some operations on arrays
      NYI_Iterators,        --  iterators
      NYI_Interface,        --  interfaces
      NYI_Class_Wide,       --  class wide types
      NYI_Unchecked,        --  unchecked expressions
      NYI_Extended_Return,  --  extended return

      --  NIR: Not In Roadmap
      --  These constructs are not in SPARK in the foreseeable future

      NIR_Access,           --  access types
      NIR_Assembly_Lang,    --  assembly language
      NIR_Dealloc,          --  deallocation
      NIR_Dynamic_Alloc,    --  dynamic allocation
      NIR_Exception,        --  exception
      NIR_Forward_Reference, --  forward reference
      NIR_Goto,             --  goto
      NIR_Indirect_Call,    --  indirect call
      NIR_Tasking,          --  tasks and protected objects
      NIR_Unchecked_Conv,   --  unchecked conversion
      NIR_Impure_Function,  --  impure functions
      NIR_Recursive,        --  disallowed recursive calls (e.g. in specs)
      NIR_Uninit_Logic_Expr, --  uninitialized logic expr
      NIR_XXX);             --  all other cases

   subtype Not_Yet_Implemented is
     Vkind range NYI_Aggregate .. NYI_Extended_Return;
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
      NYI_Attribute        => To_Unbounded_String ("attribute"),
      NYI_Concatenation    => To_Unbounded_String ("concatenation"),
      NYI_Container        => To_Unbounded_String ("container"),
      NYI_Dispatch         => To_Unbounded_String ("dispatch"),
      NYI_Expr_With_Action => To_Unbounded_String ("expression with action"),
      NYI_Invariant        => To_Unbounded_String ("type invariant"),
      NYI_Multi_Dim_Array  => To_Unbounded_String ("multi dim array"),
      NYI_Pragma           => To_Unbounded_String ("pragma"),
      NYI_Predicate        => To_Unbounded_String ("type predicate"),
      NYI_Rep_Clause       => To_Unbounded_String ("representation clause"),
      NYI_Tagged           => To_Unbounded_String ("tagged type"),
      NYI_Array_Operation  => To_Unbounded_String ("operation on arrays"),
      NYI_Iterators        => To_Unbounded_String ("iterators"),
      NYI_Class_Wide       => To_Unbounded_String ("class wide types"),
      NYI_Interface        => To_Unbounded_String ("interfaces"),
      NYI_Unchecked        => To_Unbounded_String ("unchecked expressions"),
      NYI_Extended_Return  => To_Unbounded_String ("extended return"),

      NIR_Access           => To_Unbounded_String ("access"),
      NIR_Assembly_Lang    => To_Unbounded_String ("assembly language"),
      NIR_Dealloc          => To_Unbounded_String ("deallocation"),
      NIR_Dynamic_Alloc    => To_Unbounded_String ("dynamic allocation"),
      NIR_Exception        => To_Unbounded_String ("exception"),
      NIR_Forward_Reference => To_Unbounded_String ("forward reference"),
      NIR_Goto             => To_Unbounded_String ("goto"),
      NIR_Impure_Function  => To_Unbounded_String ("impure function"),
      NIR_Indirect_Call    => To_Unbounded_String ("indirect call"),
      NIR_Tasking          => To_Unbounded_String ("tasking"),
      NIR_Unchecked_Conv   => To_Unbounded_String ("unchecked conversion"),
      NIR_Recursive        => To_Unbounded_String ("recursive call"),
      NIR_Uninit_Logic_Expr =>
                              To_Unbounded_String ("uninitialized logic expr"),
      NIR_XXX              => To_Unbounded_String ("unsupported construct"));

   function Name_Hash (N : Unbounded_String) return Hash_Type is
      (Ada.Strings.Hash (To_String (N)));

   package Name_Map is new Hashed_Maps
     (Key_Type        => Unbounded_String,
      Element_Type    => Vkind,
      Hash            => Name_Hash,
      Equivalent_Keys => "=",
      "="             => "=");

   Violation_From_Msg : Name_Map.Map;

end SPARK_Violations;
