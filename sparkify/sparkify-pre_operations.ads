------------------------------------------------------------------------------
--                                                                          --
--                            SPARKIFY COMPONENTS                           --
--                                                                          --
--               S P A R K I F Y . P R E _ O P E R A T I O N S              --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2009-2010, AdaCore                     --
--                                                                          --
-- Sparkify is  free  software;  you can redistribute it  and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. Sparkify is distributed in the hope that it will be useful, but --
-- WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHANTABI- --
-- LITY or  FITNESS  FOR A  PARTICULAR  PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- Sparkify is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

--  This package defines specific components of pre-operation for
--  Sparkify.Source_Traversal.Pre_Operation

with Asis;                             use Asis;
with Asis.Extensions.Flat_Kinds;       use Asis.Extensions.Flat_Kinds;

with Sparkify.Common;                  use Sparkify.Common;

package Sparkify.Pre_Operations is

   procedure Print_All_Use_Type (Element : Asis.Declaration);

   procedure Traverse_Element_And_Print (Element : Asis.Element);
   --  Traverse Element in Printing_Code mode (prefixing identifiers et cetera)

   procedure A_Pragma_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State);
   --  Any pragma (list below).
   --  Only the following pragmas are actually handled:
   --  * Assert
   --  * Precondition
   --  * Postcondition

   procedure A_Package_Body_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State);
   --  A_Package_Body_Declaration

   procedure A_Package_Declaration_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State);
   --  A_Package_Declaration

   procedure A_Subprogram_Unit_Declaration_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State);
   --  A_Procedure_Declaration,                   -- 6.1
   --  A_Function_Declaration,                    -- 6.1

   procedure A_Subprogram_Unit_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State);
   --  A_Function_Body_Declaration,               -- 6.3

   procedure An_Implementation_Defined_Attribute_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State);
   --  An_Implementation_Defined_Attribute,  -- Vendor Annex M

   procedure An_Identifier_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State);
   --  An_Identifier

   procedure A_Loop_Statement_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State);
   --  A_While_Loop_Statement,              -- 5.5
   --  A_For_Loop_Statement,                -- 5.5

   procedure A_Use_Package_Clause_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State);
   --  A_Use_Package_Clause

   procedure A_With_Package_Clause_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State);

   procedure An_Aggregate_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State);
   --  This extension consists in translating aggregates without a type
   --  qualifier in Ada into aggregates prefixed by the appropriate type
   --  qualifier in SPARK

   procedure An_Object_Declaration_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State);
   --  This extension consists to nominate in Spark the subtype
   --  by giving a subtype mark at the object declaration in ADA
   --  may include the definition of the (anonymous) type of the object.

   procedure A_Type_Declaration_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State);

   procedure A_Derived_Type_Definition_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State);

   Specific_Pre_Operation : array (Flat_Element_Kinds) of Op_Access :=
     (Not_An_Element => No_Action'Access,

      -------------------------------------------------------------

      --  A_Pragma,                  -- Asis.Elements

      --  Detailed classification for Asis.Element_Kinds (A_Pragma) literal,
      --  corresponds to subtype Internal_Pragma_Kinds
      ------------------------------------------------------------

      An_All_Calls_Remote_Pragma ..       -- E.2.3(4)
      --  An_Asynchronous_Pragma,           -- E.4.1(2)
      --  An_Atomic_Pragma,                 -- C.6(2)
      --  An_Atomic_Components_Pragma,      -- C.6(2)
      --  An_Attach_Handler_Pragma,         -- C.3.1(3)
      --  A_Controlled_Pragma,              -- 13.11.3(2)
      --  A_Convention_Pragma,              -- B.1(4)
      --  A_Discard_Names_Pragma,           -- C.5(2),
      --  An_Elaborate_Pragma,              -- 10.2.1(19),
      --  An_Elaborate_All_Pragma,          -- 10.2.1(19)
      --  An_Elaborate_Body_Pragma,         -- 10.2.1(19)
      --  An_Export_Pragma,                 -- B.1(4)
      --  An_Import_Pragma,                 -- B.1(4)
      --  An_Inline_Pragma,                 -- 6.3.2(2)
      --  An_Inspection_Point_Pragma,       -- H.3.2(2)
      --  An_Interrupt_Handler_Pragma,      -- C.3.1(1)
      --  An_Interrupt_Priority_Pragma,     -- D.1(4)
      --  A_Linker_Options_Pragma,          -- B.1(4),
      --  A_List_Pragma,                    -- 2.8(20)
      --  A_Locking_Policy_Pragma,          -- D.3(2)
      --  A_Normalize_Scalars_Pragma,       -- H.1(2)
      --  An_Optimize_Pragma,               -- 2.8(20)
      --  A_Pack_Pragma,                    -- 13.2(2)
      --  A_Page_Pragma,                    -- 2.8(20)
      --  A_Preelaborate_Pragma,            -- 10.2.1(2)
      --  A_Priority_Pragma,                -- D.1(2)
      --  A_Pure_Pragma,                    -- 10.2.1(13)
      --  A_Queuing_Policy_Pragma,          -- D.4(2)
      --  A_Remote_Call_Interface_Pragma,   -- E.2.3(2)
      --  A_Remote_Types_Pragma,            -- E.2.2(2)
      --  A_Restrictions_Pragma,            -- 13.12(2)
      --  A_Reviewable_Pragma,              -- H.3.1(2)
      --  A_Shared_Passive_Pragma,          -- E.2.1(2)
      --  A_Storage_Size_Pragma,            -- 13.3(62),
      --  A_Suppress_Pragma,                -- 11.5(3)
      --  A_Task_Dispatching_Policy_Pragma, -- D.2.2(2)
      --  A_Volatile_Pragma,                -- C.6(2)
      --  A_Volatile_Components_Pragma      -- C.6(2)
      --
      --  --|A2005 start
      --
      --  An_Assert_Pragma,
      --  An_Assertion_Policy_Pragma,
      --  A_Detect_Blocking_Pragma,
      --  A_No_Return_Pragma,
      --  A_Partition_Elaboration_Policy_Pragma,
      --  A_Preelaborable_Initialization_Pragma,
      --  A_Priority_Specific_Dispatching_Pragma,
      --  A_Profile_Pragma,
      --  A_Relative_Deadline_Pragma,
      --  An_Unchecked_Union_Pragma,
      --  An_Unsuppress_Pragma,
      --
      --  --|A2005 end
      --
      --  An_Implementation_Defined_Pragma,  -- 2.8(14)
      An_Unknown_Pragma => A_Pragma_Pre_Op'Access,

   ------------------------------------------------------------

   --  A_Defining_Name,           -- Asis.Declarations

   --  Detailed classification for Asis.Element_Kinds (A_Defining_Name)
   --  literal, corresponds to subtype Internal_Defining_Name_Kinds
   ------------------------------------------------------------

      A_Defining_Identifier => No_Action'Access,

      A_Defining_Character_Literal ..
      A_Defining_Enumeration_Literal =>
         No_Action'Access,

      --  A_Defining_Operator_Symbol

      --  Detailed classification for
      --  Asis.Operator_Kinds (A_Defining_Operator_Symbol) literal,
      --  corresponds to subtype Internal_Defining_Operator_Kinds

      A_Defining_And_Operator ..
      --  A_Defining_Or_Operator,                     -- or
      --  A_Defining_Xor_Operator,                    -- xor
      --  A_Defining_Equal_Operator,                  -- =
      --  A_Defining_Not_Equal_Operator,              -- /=
      --  A_Defining_Less_Than_Operator,              -- <
      --  A_Defining_Less_Than_Or_Equal_Operator,     -- <=
      --  A_Defining_Greater_Than_Operator,           -- >
      --  A_Defining_Greater_Than_Or_Equal_Operator,  -- >=
      --  A_Defining_Plus_Operator,                   -- +
      --  A_Defining_Minus_Operator,                  -- -
      --  A_Defining_Concatenate_Operator,            -- &
      --  A_Defining_Unary_Plus_Operator,             -- +
      --  A_Defining_Unary_Minus_Operator,            -- -
      --  A_Defining_Multiply_Operator,               -- *
      --  A_Defining_Divide_Operator,                 -- /
      --  A_Defining_Mod_Operator,                    -- mod
      --  A_Defining_Rem_Operator,                    -- rem
      --  A_Defining_Exponentiate_Operator,           -- **
      --  A_Defining_Abs_Operator,                    -- abs
      A_Defining_Not_Operator => No_Action'Access,
      --

      A_Defining_Expanded_Name => No_Action'Access,

      --                        6.1 program_unit_name.defining_identifier
      --
      ------------------------------------------------------------

      --  A_Declaration,             -- Asis.Declarations

      --  Detailed classification for
      --  Asis.Element_Kinds (A_Declaration) literal
      --  corresponds to subtype Internal_Declaration_Kinds
      ------------------------------------------------------------

      An_Ordinary_Type_Declaration =>
         A_Type_Declaration_Pre_Op'Access,

      A_Task_Type_Declaration ..
      A_Protected_Type_Declaration => No_Action'Access,

      An_Incomplete_Type_Declaration ..

      --  A_Private_Type_Declaration,                -- 3.2.1
      --  A_Private_Extension_Declaration,           -- 3.2.1
      --

      A_Subtype_Declaration => No_Action'Access,

      A_Variable_Declaration ..
      --  A_Constant_Declaration,                    -- 3.3.1 -> Trait_Kinds
      A_Deferred_Constant_Declaration => An_Object_Declaration_Pre_Op'Access,

      A_Single_Task_Declaration ..
      A_Single_Protected_Declaration => No_Action'Access,

      --
      An_Integer_Number_Declaration ..
      A_Real_Number_Declaration => No_Action'Access,

      An_Enumeration_Literal_Specification => No_Action'Access,

      A_Discriminant_Specification => No_Action'Access,

      A_Component_Declaration => No_Action'Access,

      A_Loop_Parameter_Specification => No_Action'Access,

      A_Procedure_Declaration ..
      A_Function_Declaration => A_Subprogram_Unit_Declaration_Pre_Op'Access,

      A_Parameter_Specification => No_Action'Access,

      A_Procedure_Body_Declaration ..
      A_Function_Body_Declaration       => A_Subprogram_Unit_Pre_Op'Access,

      A_Return_Object_Declaration  => No_Action'Access,
      A_Null_Procedure_Declaration => No_Action'Access,

      A_Package_Declaration => A_Package_Declaration_Pre_Op'Access,
      A_Package_Body_Declaration => A_Package_Body_Pre_Op'Access,

      --
      An_Object_Renaming_Declaration ..
      An_Exception_Renaming_Declaration => No_Action'Access,

      A_Package_Renaming_Declaration ..
      --  A_Procedure_Renaming_Declaration,          -- 8.5.4
      --  A_Function_Renaming_Declaration,           -- 8.5.4
      --  A_Generic_Package_Renaming_Declaration,    -- 8.5.5
      --  A_Generic_Procedure_Renaming_Declaration,  -- 8.5.5
      A_Generic_Function_Renaming_Declaration => No_Action'Access,

      A_Task_Body_Declaration ..
      A_Protected_Body_Declaration => No_Action'Access,

      An_Entry_Declaration => No_Action'Access,

      An_Entry_Body_Declaration =>  No_Action'Access,

      An_Entry_Index_Specification => No_Action'Access,

      A_Procedure_Body_Stub ..
      --  A_Function_Body_Stub,                      -- 10.1.3
      --  A_Package_Body_Stub,                       -- 10.1.3
      --  A_Task_Body_Stub,                          -- 10.1.3
      A_Protected_Body_Stub => No_Action'Access,

      An_Exception_Declaration => No_Action'Access,

      A_Choice_Parameter_Specification => No_Action'Access,

      A_Generic_Procedure_Declaration ..
      --  A_Generic_Function_Declaration,            -- 12.1
      A_Generic_Package_Declaration => No_Action'Access,

      A_Package_Instantiation ..
      --  A_Procedure_Instantiation,                 -- 12.3
      A_Function_Instantiation => No_Action'Access,
      --

      A_Formal_Object_Declaration => No_Action'Access,

      A_Formal_Type_Declaration => No_Action'Access,

      A_Formal_Procedure_Declaration ..
      A_Formal_Function_Declaration =>
         No_Action'Access,

      A_Formal_Package_Declaration => No_Action'Access,

      A_Formal_Package_Declaration_With_Box =>
         No_Action'Access,

      --
      ------------------------------------------------------------

      --  A_Definition,              --  Asis.Definitions
      --
      --  Detailed classification for Asis.Element_Kinds (A_Definition)
      --  literal, corresponds to subtype Internal_Definition_Kinds
      ------------------------------------------------------------

      --  A_Type_Definition,                -- 3.2.1   -> Type_Kinds

      --  Detailed classification for Asis.Definition_Kinds (A_Type_Definition)
      --  literal, corresponds to subtype Internal_Type_Kinds

      A_Derived_Type_Definition => A_Derived_Type_Definition_Pre_Op'Access,

      A_Derived_Record_Extension_Definition => No_Action'Access,

      An_Enumeration_Type_Definition => No_Action'Access,

      A_Signed_Integer_Type_Definition => No_Action'Access,

      A_Modular_Type_Definition => No_Action'Access,

   --     A_Root_Type_Definition,                -- 3.5.4(10), 3.5.6(4)
   --                                                      -> Root_Type_Kinds
   --  Detailed classification for Asis.Type_Kinds (A_Root_Type_Definition)
   --  literal, corresponds to subtype Internal_Root_Type_Kinds

      A_Root_Integer_Definition ..
      --  A_Root_Real_Definition,                -- 3.5.6(2)
      --
      --  A_Universal_Integer_Definition,        -- 3.5.4(10)
      --  A_Universal_Real_Definition,           -- 3.5.6(4)
      A_Universal_Fixed_Definition => No_Action'Access,

      A_Floating_Point_Definition => No_Action'Access,

      An_Ordinary_Fixed_Point_Definition ..
      A_Decimal_Fixed_Point_Definition => No_Action'Access,

      An_Unconstrained_Array_Definition ..
      A_Constrained_Array_Definition => No_Action'Access,

      --
      A_Record_Type_Definition ..
      A_Tagged_Record_Type_Definition =>
         No_Action'Access,

      An_Ordinary_Interface ..
      --  A_Limited_Interface,             -- limited interface ...
      --  A_Task_Interface,                -- task interface ...
      --  A_Protected_Interface,           -- protected interface ...
      A_Synchronized_Interface => No_Action'Access,

   --     An_Access_Type_Definition,             -- 3.10   -> Access_Type_Kinds

   --  Detailed classification for
   --  Asis.Type_Kinds (An_Access_Type_Definition) literal,
   --  corresponds to subtype Internal_Access_Type_Kinds

      A_Pool_Specific_Access_To_Variable ..
      --  An_Access_To_Variable,              -- access all subtype_indication
      An_Access_To_Constant => No_Action'Access,
      --

      An_Access_To_Procedure ..
      --  An_Access_To_Protected_Procedure,   -- access protected procedure
      --  An_Access_To_Function,              -- access function
      An_Access_To_Protected_Function => No_Action'Access,

--      A_Subtype_Indication => No_Action'Access,
      A_Subtype_Indication => No_Action'Access,

   --  A_Constraint,                     -- 3.2.2   -> Constraint_Kinds

   --  Detailed classification for Asis.Definition_Kinds (A_Constraint)
   --  literal, corresponds to subtype Internal_Constraint_Kinds

      A_Range_Attribute_Reference => No_Action'Access,

      A_Simple_Expression_Range => No_Action'Access,

      A_Digits_Constraint => No_Action'Access,
      A_Delta_Constraint => No_Action'Access,

      An_Index_Constraint => No_Action'Access,

      A_Discriminant_Constraint => No_Action'Access,

      A_Component_Definition => No_Action'Access,

      --  A_Discrete_Subtype_Definition,    -- 3.6     -> Discrete_Range_Kinds

      --  Detailed classification for
      --  Asis.Definition_Kinds (A_Discrete_Subtype_Definition) literal,
      --  corresponds to subtype Internal_Discrete_Subtype_Definition_Kinds

      A_Discrete_Subtype_Indication_As_Subtype_Definition ..
      --  A_Discrete_Range_Attribute_Reference_As_Subtype_Definition,
      --                                                          -- 3.6.1, 3.5
      A_Discrete_Simple_Expression_Range_As_Subtype_Definition
         => No_Action'Access,

      --  There is no syntactical difference between
      --  A_Discrete_Subtype_Definition kinds and A_Discrete_Range kinds, the
      --  difference is in the context in which they occur - the first defines
      --  subtype in an array type definition, the second should corresponds to
      --  some existing subtype in a range constraint
      --
      --  This is the case when in the ASIS-defined Element classification
      --  we have a net instead of a hierarchy

      --  A_Discrete_Range,                 -- 3.6.1   -> Discrete_Range_Kinds

      --  Detailed classification for Asis.Definition_Kinds (A_Discrete_Range)
      --  literal, corresponds to subtype Internal_Discrete_Range_Kinds

      A_Discrete_Subtype_Indication ..
      --  A_Discrete_Range_Attribute_Reference => No_Action'Access,
        A_Discrete_Simple_Expression_Range =>
          No_Action'Access,

      An_Unknown_Discriminant_Part => No_Action'Access,

      A_Known_Discriminant_Part => No_Action'Access,

      A_Record_Definition => No_Action'Access,

      A_Null_Record_Definition => No_Action'Access,

      A_Null_Component => No_Action'Access,

      A_Variant_Part => No_Action'Access,

      A_Variant => No_Action'Access,

      An_Others_Choice => No_Action'Access,

      An_Anonymous_Access_To_Variable ..
      An_Anonymous_Access_To_Constant => No_Action'Access,

      An_Anonymous_Access_To_Procedure ..
      --  An_Anonymous_Access_To_Protected_Procedure,
      --  An_Anonymous_Access_To_Function,
      An_Anonymous_Access_To_Protected_Function =>
        No_Action'Access,

      A_Private_Type_Definition ..
      A_Tagged_Private_Type_Definition =>
         No_Action'Access,

      A_Private_Extension_Definition =>
         No_Action'Access,

      A_Task_Definition => No_Action'Access,

      A_Protected_Definition => No_Action'Access,

      --
      --  A_Formal_Type_Definition,         -- 12.5    -> Formal_Type_Kinds

      --  Detailed classification for
      --  Asis.Definition_Kinds (A_Formal_Type_Definition) literal,
      --  corresponds to subtype Internal_Formal_Type_Kinds

       A_Formal_Private_Type_Definition ..
       A_Formal_Tagged_Private_Type_Definition =>
          No_Action'Access,

      A_Formal_Derived_Type_Definition =>
        No_Action'Access,

      A_Formal_Discrete_Type_Definition ..
      --  A_Formal_Signed_Integer_Type_Definition
      --  A_Formal_Modular_Type_Definition,         -- 12.5.2
      --
      --  A_Formal_Floating_Point_Definition,       -- 12.5.2
      --
      --  A_Formal_Ordinary_Fixed_Point_Definition, -- 12.5.2
      A_Formal_Decimal_Fixed_Point_Definition
         => No_Action'Access,

      A_Formal_Ordinary_Interface ..
      --  A_Formal_Limited_Interface
      --  A_Formal_Task_Interface
      --  A_Formal_Protected_Interface
      A_Formal_Synchronized_Interface => No_Action'Access,

      A_Formal_Unconstrained_Array_Definition ..
      A_Formal_Constrained_Array_Definition =>
         No_Action'Access,

      --   A_Formal_Access_Type_Definition,     -- 12.5.4  -> Access_Type_Kinds

      --  Detailed classification for
      --  Asis.Definition_Kinds.Internal_Formal_Type_Kinds
      --  (A_Formal_Access_Type_Definition) literal,
      --  corresponds to subtype Internal_Formal_Access_Type_Kinds

      A_Formal_Pool_Specific_Access_To_Variable ..
      --                                    -- access subtype_indication
      --  A_Formal_Access_To_Variable,        -- access all subtype_indication
      A_Formal_Access_To_Constant => No_Action'Access,

      A_Formal_Access_To_Procedure ..
      --  A_Formal_Access_To_Protected_Procedure, -- access protected procedure
      --  A_Formal_Access_To_Function,               -- access function
      A_Formal_Access_To_Protected_Function =>
         No_Action'Access,

      ------------------------------------------------------------

      --  An_Expression,             -- Asis.Expressions

      --  Detailed classification for Asis.Element_Kinds (An_Expression)
      --  literal corresponds to subtype Internal_Expression_Kinds
      ------------------------------------------------------------

      An_Integer_Literal ..
      --  A_Real_Literal,                            -- 2.4.1
      A_String_Literal => No_Action'Access,

      An_Identifier => An_Identifier_Pre_Op'Access,

      --  An_Operator_Symbol,                        -- 4.1

      --  Detailed classification for
      --  Asis.Expression_Kinds (An_Operator_Symbol) literal
      --  corresponds to subtype Internal_Operator_Symbol_Kinds

      An_And_Operator ..
      --  An_Or_Operator,                      -- or
      --  An_Xor_Operator,                     -- xor
      --  An_Equal_Operator,                   -- =
      --  A_Not_Equal_Operator,                -- /=
      --  A_Less_Than_Operator,                -- <
      --  A_Less_Than_Or_Equal_Operator,       -- <=
      --  A_Greater_Than_Operator,             -- >
      --  A_Greater_Than_Or_Equal_Operator,    -- >=
      --  A_Plus_Operator,                     -- +
      --  A_Minus_Operator,                    -- -
      --  A_Concatenate_Operator,              -- &
      --  A_Unary_Plus_Operator,               -- +
      --  A_Unary_Minus_Operator,              -- -
      --  A_Multiply_Operator,                 -- *
      --  A_Divide_Operator,                   -- /
      --  A_Mod_Operator,                      -- mod
      --  A_Rem_Operator,                      -- rem
      --  An_Exponentiate_Operator,            -- **
      --  An_Abs_Operator,                     -- abs
      A_Not_Operator => No_Action'Access,
      --

      A_Character_Literal => No_Action'Access,
      An_Enumeration_Literal => An_Identifier_Pre_Op'Access,

      An_Explicit_Dereference => No_Action'Access,

      A_Function_Call => No_Action'Access,

      An_Indexed_Component ..
      A_Slice => No_Action'Access,

      A_Selected_Component => No_Action'Access,

      --
      --  An_Attribute_Reference,                    -- 4.1.4

      --  Detailed classification for
      --  Asis.Expression_Kinds (An_Attribute_Reference) literal
      --  corresponds to subtype Internal_Attribute_Reference_Kinds

      An_Access_Attribute ..
      --  An_Address_Attribute,          -- 13.3(11), J.7.1(5), K(6)
      --  An_Adjacent_Attribute,         -- A.5.3(48), K(8)
      --  An_Aft_Attribute,              -- 3.5.10(5), K(12)
      --  An_Alignment_Attribute,        -- 13.3(23), K(14)
      --  A_Base_Attribute,              -- 3.5(15), K(17)
      --  A_Bit_Order_Attribute,         -- 13.5.3(4), K(19)
      --  A_Body_Version_Attribute,      -- E.3(4), K(21)
      --  A_Callable_Attribute,          -- 9.9(2), K(23)
      --  A_Caller_Attribute,            -- C.7.1(14), K(25)
      --  A_Ceiling_Attribute,           -- A.5.3(33), K(27)
      --  A_Class_Attribute,             -- 3.9(14), 7.3.1(9), K(31), K(34)
      --  A_Component_Size_Attribute,    -- 13.3(69), K(36)
      --  A_Compose_Attribute,           -- A.5.3(24), K(38)
      --  A_Constrained_Attribute,       -- 3.7.2(3), J.4(2), K(42)
      --  A_Copy_Sign_Attribute,         -- A.5.3(51), K(44)
      --  A_Count_Attribute,             -- 9.9(5), K(48)
      --  A_Definite_Attribute,          -- 12.5.1(23), K(50)
      --  A_Delta_Attribute,             -- 3.5.10(3), K(52)
      --  A_Denorm_Attribute,            -- A.5.3(9), K(54)
      --  A_Digits_Attribute,            -- 3.5.8(2), 3.5.10(7), K(56), K(58)
      --  An_Exponent_Attribute,         -- A.5.3(18), K(60)
      --  An_External_Tag_Attribute,     -- 13.3(75), K(64)
      --  A_First_Attribute,             -- 3.5(12), 3.6.2(3), K(68), K(70)
      --  A_First_Bit_Attribute,         -- 13.5.2(3), K(72)
      --  A_Floor_Attribute,             -- A.5.3(30), K(74)
      --  A_Fore_Attribute,              -- 3.5.10(4), K(78)
      --  A_Fraction_Attribute,          -- A.5.3(21), K(80)
      --  An_Identity_Attribute,         -- 11.4.1(9), C.7.1(12), K(84), K(86)
      --  An_Image_Attribute,            -- 3.5(35), K(88)
      --  An_Input_Attribute,        -- 13.13.2(22), 13.13.2(32), K(92), K(96)
      --  A_Last_Attribute,              -- 3.5(13), 3.6.2(5), K(102), K(104)
      --  A_Last_Bit_Attribute,          -- 13.5.2(4), K(106)
      --  A_Leading_Part_Attribute,      -- A.5.3(54), K(108)
      --  A_Length_Attribute,            -- 3.6.2(9), K(117)
      --  A_Machine_Attribute,           -- A.5.3(60), K(119)
      --  A_Machine_Emax_Attribute,      -- A.5.3(8), K(123)
      --  A_Machine_Emin_Attribute,      -- A.5.3(7), K(125)
      --  A_Machine_Mantissa_Attribute,  -- A.5.3(6), K(127)
      --  A_Machine_Overflows_Attribute, -- A.5.3(12), A.5.4(4), K(129), K(131)
      --  A_Machine_Radix_Attribute,     -- A.5.3(2), A.5.4(2), K(133), K(135)
      --  A_Machine_Rounds_Attribute,    -- A.5.3(11), A.5.4(3), K(137), K(139)
      --  A_Max_Attribute,               -- 3.5(19), K(141)
      --  A_Max_Size_In_Storage_Elements_Attribute, --   13.11.1(3), K(145)
      --  A_Min_Attribute,               -- 3.5(16), K(147)
      --  A_Model_Attribute,             -- A.5.3(68), G.2.2(7), K(151)
      --  A_Model_Emin_Attribute,        -- A.5.3(65), G.2.2(4), K(155)
      --  A_Model_Epsilon_Attribute,     -- A.5.3(66), K(157)
      --  A_Model_Mantissa_Attribute,    -- A.5.3(64), G.2.2(3), K(159)
      --  A_Model_Small_Attribute,       -- A.5.3(67), K(161)
      --  A_Modulus_Attribute,           -- 3.5.4(17), K(163)
      --  An_Output_Attribute,     -- 13.13.2(19), 13.13.2(29), K(165), K(169)
      --  A_Partition_ID_Attribute,      -- E.1(9), K(173)
      --  A_Pos_Attribute,               -- 3.5.5(2), K(175)
      --  A_Position_Attribute,          -- 13.5.2(2), K(179)
      --  A_Pred_Attribute,              -- 3.5(25), K(181)
      --  A_Range_Attribute,             -- 3.5(14), 3.6.2(7), K(187), K(189)
      --  A_Read_Attribute,         -- 13.13.2(6), 13.13.2(14), K(191), K(195)
      --  A_Remainder_Attribute,         -- A.5.3(45), K(199)
      --  A_Round_Attribute,             -- 3.5.10(12), K(203)
      --  A_Rounding_Attribute,          -- A.5.3(36), K(207)
      --  A_Safe_First_Attribute,        -- A.5.3(71), G.2.2(5), K(211)
      --  A_Safe_Last_Attribute,         -- A.5.3(72), G.2.2(6), K(213)
      --  A_Scale_Attribute,             -- 3.5.10(11), K(215)
      --  A_Scaling_Attribute,           -- A.5.3(27), K(217)
      --  A_Signed_Zeros_Attribute,      -- A.5.3(13), K(221)
      --  A_Size_Attribute,              -- 13.3(40), 13.3(45), K(223), K(228)
      --  A_Small_Attribute,             -- 3.5.10(2), K(230)
      --  A_Storage_Pool_Attribute,      -- 13.11(13), K(232)
      --  A_Storage_Size_Attribute,     -- 13.3(60), 13.11(14), J.9(2), K(234),
      --  --                                K(236)
      --  A_Succ_Attribute,              -- 3.5(22), K(238)
      --  A_Tag_Attribute,               -- 3.9(16), 3.9(18), K(242), K(244)
      --  A_Terminated_Attribute,        -- 9.9(3), K(246)
      --  A_Truncation_Attribute,        -- A.5.3(42), K(248)
      --  An_Unbiased_Rounding_Attribute, -- A.5.3(39), K(252)
      --  An_Unchecked_Access_Attribute, -- 13.10(3), H.4(18), K(256)
      --  A_Val_Attribute,               -- 3.5.5(5), K(258)
      --  A_Valid_Attribute,             -- 13.9.2(3), H(6), K(262)
      --  A_Value_Attribute,             -- 3.5(52), K(264)
      --  A_Version_Attribute,           -- E.3(3), K(268)
      --  A_Wide_Image_Attribute,        -- 3.5(28), K(270)
      --  A_Wide_Value_Attribute,        -- 3.5(40), K(274)
      --  A_Wide_Width_Attribute,        -- 3.5(38), K(278)
      --  A_Width_Attribute,             -- 3.5(39), K(280)
      A_Write_Attribute => No_Action'Access,
      An_Implementation_Defined_Attribute =>
        An_Implementation_Defined_Attribute_Pre_Op'Access,
      An_Unknown_Attribute => No_Action'Access,

      A_Record_Aggregate ..
      --  An_Extension_Aggregate,                    -- 4.3
      --  A_Positional_Array_Aggregate,              -- 4.3
      A_Named_Array_Aggregate => An_Aggregate_Pre_Op'Access,

      An_And_Then_Short_Circuit ..
      An_Or_Else_Short_Circuit => No_Action'Access,

      An_In_Range_Membership_Test ..
      --  A_Not_In_Range_Membership_Test,            -- 4.4
      --  An_In_Type_Membership_Test,                -- 4.4
      A_Not_In_Type_Membership_Test => No_Action'Access,

      A_Null_Literal => No_Action'Access,

      A_Parenthesized_Expression => No_Action'Access,

      A_Type_Conversion ..
      A_Qualified_Expression => No_Action'Access,

      An_Allocation_From_Subtype ..
      An_Allocation_From_Qualified_Expression => No_Action'Access,

      ------------------------------------------------------------

      --  An_Association,            -- Asis.Expressions

      --  Detailed classification for Asis.Element_Kinds (An_Association)
      --  literal corresponds to subtype Internal_Association_Kinds
      ------------------------------------------------------------

      A_Pragma_Argument_Association ..
      --  A_Discriminant_Association,            -- 3.7.1
      --  A_Record_Component_Association,        -- 4.3.1
      --  An_Array_Component_Association,        -- 4.3.3
      --  A_Parameter_Association,               -- 6.4
      A_Generic_Association => No_Action'Access,

      --
      ------------------------------------------------------------

      --  A_Statement,               -- Asis.Statements

      --  Detailed classification for Asis.Element_Kinds (A_Statement) literal
      --  corresponds to subtype Internal_Statement_Kinds
      ------------------------------------------------------------

      A_Null_Statement => No_Action'Access,

      An_Assignment_Statement => No_Action'Access,

      An_If_Statement => No_Action'Access,

      A_Case_Statement => No_Action'Access,

      --
      A_Loop_Statement ..
      --  A_While_Loop_Statement,              -- 5.5
      A_For_Loop_Statement => A_Loop_Statement_Pre_Op'Access,
      A_Block_Statement => No_Action'Access,

      An_Exit_Statement              => No_Action'Access,
      A_Goto_Statement               => No_Action'Access,
      A_Procedure_Call_Statement     => No_Action'Access,
      A_Return_Statement             => No_Action'Access,
      An_Extended_Return_Statement   => No_Action'Access,
      An_Accept_Statement            => No_Action'Access,
      An_Entry_Call_Statement        => No_Action'Access,
      A_Requeue_Statement            => No_Action'Access,
      A_Requeue_Statement_With_Abort => No_Action'Access,

      A_Delay_Until_Statement ..
      A_Delay_Relative_Statement => No_Action'Access,

      A_Terminate_Alternative_Statement => No_Action'Access,

      A_Selective_Accept_Statement => No_Action'Access,

      A_Timed_Entry_Call_Statement ..
      --  A_Conditional_Entry_Call_Statement,  -- 9.7.3
      --  An_Asynchronous_Select_Statement,    -- 9.7.4
      --
      --  An_Abort_Statement,                  -- 9.8

      A_Raise_Statement => No_Action'Access,

      A_Code_Statement => No_Action'Access,

      ------------------------------------------------------------
      --  Path_Kinds
      --  Literals                        -- Ada RM
      --
      --  Detailed classification for Asis.Element_Kinds (A_Path) literal
      --  corresponds to subtype Internal_Path_Kinds
      ------------------------------------------------------------

      An_If_Path ..
      --                                 if condition then
      --                                   sequence_of_statements

      --  An_Elsif_Path,                  -- 5.3:
      --                                 elsif condition then
      --                                   sequence_of_statements

      An_Else_Path => No_Action'Access,
      --                                 else sequence_of_statements

      A_Case_Path => No_Action'Access,

      A_Select_Path ..
      --                                 select [guard] select_alternative
      --                                 9.7.2, 9.7.3:
      --                                 select entry_call_alternative
      --                                 9.7.4:
      --                                 select triggering_alternative

      An_Or_Path => No_Action'Access,

      --                                 or [guard] select_alternative
      --                                 9.7.2:
      --                                 or delay_alternative

      A_Then_Abort_Path => No_Action'Access,
      --                                 then abort sequence_of_statements

      ------------------------------------------------------------

      --  A_Clause,                  -- Asis.Clauses

      --  Detailed classification for Asis.Element_Kinds (A_Clause) literal
      --  corresponds to subtype Internal_Clause_Kinds
      ------------------------------------------------------------

      A_Use_Package_Clause => A_Use_Package_Clause_Pre_Op'Access,

      A_Use_Type_Clause => No_Action'Access,

      A_With_Clause => A_With_Package_Clause_Pre_Op'Access,

      --  A_Representation_Clause,  -- 13.1     -> Representation_Clause_Kinds

      --  Detailed classification for
      --  Asis.Clause_Kinds (A_Representation_Clause) literal,
      --  corresponds to subtype Internal_Representation_Clause_Kinds

      An_Attribute_Definition_Clause => No_Action'Access,

      An_Enumeration_Representation_Clause =>
         No_Action'Access,

      A_Record_Representation_Clause =>
         No_Action'Access,

      An_At_Clause => No_Action'Access,

      A_Component_Clause => No_Action'Access,

      An_Exception_Handler => No_Action'Access,

      others => Non_Implemented_ASIS_2005_Feature'Access);

end Sparkify.Pre_Operations;
