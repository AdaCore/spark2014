------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                              V C _ K I N D S                             --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2023, AdaCore                     --
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

--  This package defines the different kinds of VCs that we generate in
--  Gnat2why. The run-time checks correspond to Ada RM checks, for which the
--  front-end defines distinct constants in types.ads. Here, we use a new
--  enumeration instead of these constants, because we are only interested in
--  run-time errors that can happen in SPARK code (e.g. it excludes
--  Access_Check), and which GNATprove can detect (it excludes
--  Storage_Check), plus various assertions that we want to distinguish.

--  Changes in VC_Kind should be reflected in
--    - file gnat_expl.ml in gnatwhy3
--    - GPS plug-in spark2014.py

with Ada.Containers.Doubly_Linked_Lists;
with Ada.Containers.Indefinite_Doubly_Linked_Lists;
with Ada.Containers.Indefinite_Ordered_Maps;
with Ada.Containers.Ordered_Maps;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with GNATCOLL.JSON;         use GNATCOLL.JSON;
with String_Utils;          use String_Utils;

package VC_Kinds is

   type VC_Kind is
      --  VC_RTE_Kind - run-time checks

     (VC_Division_Check,
      VC_Index_Check,
      VC_Overflow_Check,
      VC_FP_Overflow_Check,
      VC_Range_Check,
      VC_Predicate_Check,
      VC_Predicate_Check_On_Default_Value,  --  the predicate check on
                                            --  the default value of a type,
                                            --  to be used when a value of the
                                            --  type is default initialized
      VC_Null_Pointer_Dereference,
      --  This VC is to be used whenever we try to dereference an object
      --  with access type. This check should be done on the _is_null_pointer
      --  field of the why record corresponding to the pointer type.

      VC_Null_Exclusion,
      VC_Dynamic_Accessibility_Check,
      VC_Resource_Leak,
      VC_Resource_Leak_At_End_Of_Scope,

      VC_Unchecked_Union_Restriction, --  Specific restrictions for types
                                      --  with Unchecked_Union occuring in
                                      --  equality, membership tests, and
                                      --  type conversions

      VC_Length_Check,
      VC_Discriminant_Check,
      VC_Tag_Check,
      VC_Ceiling_Interrupt,
      VC_Initialization_Check,
      VC_Interrupt_Reserved,
      VC_Invariant_Check,
      VC_Invariant_Check_On_Default_Value,  --  the invariant check on
                                            --  the default value of a type,
                                            --  it is used once at the type
                                            --  declaration.
      VC_Ceiling_Priority_Protocol,
      VC_Task_Termination,

      --  VC_Assert_Kind - assertions

      VC_Initial_Condition,
      VC_Default_Initial_Condition,
      VC_Precondition,               --  the precondition of a call
      VC_Precondition_Main,          --  the precondition of a main program
      VC_Postcondition,              --  a postcondition
      VC_Refined_Post,               --  a refined_post
      VC_Contract_Case,
      VC_Disjoint_Contract_Cases,
      VC_Complete_Contract_Cases,
      VC_Exceptional_Case,
      VC_Loop_Invariant,             --  internal check kind, transformed
                                     --  by gnatwhy3 into
                                     --    VC_Loop_Invariant_Init
                                     --  or
                                     --    VC_Loop_Invariant_Preserv
      VC_Loop_Invariant_Init,
      VC_Loop_Invariant_Preserv,
      VC_Loop_Variant,
      VC_Subprogram_Variant,
      VC_Assert,
      VC_Assert_Step,                --  Side condition for proof cut points
      VC_Assert_Premise,             --  Premise for proof with cut points
      VC_Raise,
      VC_Feasible_Post,              --  Check that the postcondition of
                                     --  abstract functions and
                                     --  access-to-function types are feasible.
      VC_Inline_Check,               --  Check that the Inline_For_Proof or
                                     --  Logical_Equal annotation provided for
                                     --  a function is correct.

      VC_UC_Source,                  --  Check that this type is suitable as a
                                    --  source for an Unchecked_Conversion
      VC_UC_Target,                  --  Check that this type is suitable as a
                                    --  target for an Unchecked_Conversion

      VC_UC_Same_Size,               --  Check that the two types of an
                                    --  Unchecked_Conversion are of the same
                                    --  size

      VC_UC_Alignment,                --  Check that the two objects
                                      --  in an overlay have compatible
                                      --  alignments

      VC_UC_Volatile,                 --  Check that we specify the address of
                                      --  an object only if it is volatile, or
                                      --  the address clause is "simple"

      --  VC_LSP_Kind - Liskov Substitution Principle

      VC_Weaker_Pre,                  --  pre weaker than classwide pre
      VC_Trivial_Weaker_Pre,          --  specialization of VC_Weaker_Pre when
                                      --  there is no classwide or inherited
                                      --  precondition
      VC_Stronger_Post,               --  post stronger than classwide post
      VC_Weaker_Classwide_Pre,        --  classwide pre weaker than inherited
      VC_Stronger_Classwide_Post,     --  classwide post stronger t/ inherited

      VC_Weaker_Pre_Access,           --  pre of source is weaker than pre of
                                       --  target.
      VC_Stronger_Post_Access,        --  post of source is stronger than post
                                       --  of target.

      --  VC_Warning_Kind - warnings

      VC_Inconsistent_Pre,
      VC_Inconsistent_Post,
      VC_Inconsistent_Assume,
      VC_Unreachable_Branch,
      VC_Dead_Code);

   subtype VC_Overflow_Kind is VC_Kind range
     VC_Overflow_Check .. VC_FP_Overflow_Check;

   subtype VC_Range_Kind is VC_Kind with
     Static_Predicate =>
       VC_Range_Kind in VC_Overflow_Check
                      | VC_FP_Overflow_Check
                      | VC_Range_Check
                      | VC_Length_Check
                      | VC_Index_Check;

   subtype VC_RTE_Kind is VC_Kind range
     VC_Division_Check .. VC_Task_Termination;

   subtype VC_Assert_Kind is VC_Kind range
     VC_Initial_Condition .. VC_UC_Volatile;

   subtype VC_LSP_Kind is VC_Kind range
     VC_Weaker_Pre .. VC_Stronger_Post_Access;

   subtype VC_Warning_Kind is VC_Kind range
     VC_Inconsistent_Pre .. VC_Dead_Code;

   subtype Proof_High_Severity_Kind is VC_Kind
     with Predicate =>
       Proof_High_Severity_Kind in
         VC_UC_Source
       | VC_UC_Target
       | VC_UC_Same_Size
       | VC_UC_Alignment
       | VC_UC_Volatile
       | VC_Unchecked_Union_Restriction;
   --  Subtype used to indicate VC kinds that have high severity if unproved.
   --  We use a subtype predicate rather than a range to allow for
   --  non-consecutive entries.

   type Flow_Tag_Kind is
     (Empty_Tag,
      --  Used when a tag is not specified, only for errors/warnings not checks

      --  Flow_Error_Kind - errors
      ----------------------------

      Critical_Global_Missing,
      --  There is a critical variable missing from the Globals

      Non_Volatile_Function_With_Volatile_Effects,
      --  Non Volatile_Function refers to globals with volatile effects

      Side_Effects,
      --  A function with side-effects has been found

      --  Flow_Check_Kind - checks
      ----------------------------

      Aliasing,
      --  Used for aliasing checks

      Call_In_Type_Invariant,
      --  Call to boundary program of a type from its type invariant

      Call_To_Current_Task,
      --  Call to Current_Task from invalid context

      Concurrent_Access,
      --  Global data is accessed concurrently by tasks

      Default_Initialization_Mismatch,
      --  A type marked as Fully_Default_Initialized is not fully initialized

      Depends_Missing,
      --  There is a variable missing from the RHS of a dependency

      Depends_Missing_Clause,
      --  There is an entire clause missing from the Depends contract

      Depends_Null,
      --  There is a missing dependency of the format "null => something"

      Depends_Wrong,
      --  User provided an incorrect dependency

      Export_Depends_On_Proof_In,
      --  A Proof_In variable has been used in the computation of an export

      Ghost_Wrong,
      --  A ghost procedure has a non-ghost global output

      Global_Missing,
      --  There is a variable missing from the Globals

      Global_Wrong,
      --  User provided a wrong global

      Hidden_Unexposed_State,
      --  Some hidden state has not been exposed through a state abstraction

      Illegal_Update,
      --  Writing to a variable which is not a global Output of the subprogram,
      --  or not a variable of the package during its elaboration.

      Initializes_Wrong,
      --  User provided an incorrect Initializes contract

      Missing_Return,
      --  Function has a path without a return statement

      Not_Constant_After_Elaboration,
      --  Variable that has been marked as Constant_After_Elaboration
      --  can potentially be updated.

      Potentially_Blocking_In_Protected,
      --  Protected operation calls potentially blocking feature

      Reference_To_Non_CAE_Variable,
      --  The precondition of a protected operation refers to a global
      --  variable that does not have Constant_After_Elaboration set.

      Refined_State_Wrong,
      --  User provided an incorrect Refined_State contract

      Subprogram_Termination,
      --  A subprogram with annotation Terminating may not terminate

      Uninitialized,
      --  Use of an uninitialized variable

      Unused_Global,
      --  A global has not been used

      --  Flow_Warning_Kind - warnings
      --------------------------------

      Dead_Code,
      --  Statement is never reached

      Impossible_To_Initialize_State,
      --  A state abstraction cannot possibly be initialized

      Ineffective,
      --  Code has no effect on any exports

      Inout_Only_Read,
      --  Inout could have been an In

      Stable,
      --  Found a stable element inside a loop (this has not been
      --  implemented yet).

      Unused_Variable,
      --  A variable has not been used

      Unused_Initial_Value,
      --  Initial value has not been used

      Volatile_Function_Without_Volatile_Effects
      --  Function has been marked as volatile but has no volatile effects

     );
   pragma Ordered (Flow_Tag_Kind);

   subtype Flow_Error_Kind is Flow_Tag_Kind range
     Critical_Global_Missing .. Side_Effects;

   subtype Flow_Check_Kind is Flow_Tag_Kind range
     Aliasing .. Unused_Global;

   subtype Flow_Warning_Kind is Flow_Tag_Kind range
     Dead_Code .. Volatile_Function_Without_Volatile_Effects;

   subtype Valid_Flow_Tag_Kind is Flow_Tag_Kind range
     Flow_Tag_Kind'Succ (Empty_Tag) .. Flow_Tag_Kind'Last;
   --  Non-empty tags

   --  Each valid flow analysis kind is exactly one of error/check/warning
   pragma Assert (for all Kind in Valid_Flow_Tag_Kind =>
                    (if Kind in Flow_Error_Kind then 1 else 0)
                  + (if Kind in Flow_Check_Kind then 1 else 0)
                  + (if Kind in Flow_Warning_Kind then 1 else 0)
                  = 1);

   subtype Data_Dependency_Tag is Flow_Tag_Kind with
     Static_Predicate => Data_Dependency_Tag in
         Global_Missing
       | Global_Wrong
       | Export_Depends_On_Proof_In
       | Illegal_Update
       | Not_Constant_After_Elaboration;
   --  Tags reported as data dependency errors

   subtype Flow_Dependency_Tag is Flow_Tag_Kind with
     Static_Predicate => Flow_Dependency_Tag in
         Depends_Null
       | Depends_Missing
       | Depends_Missing_Clause
       | Depends_Wrong
       | Initializes_Wrong;
   --  Tags reported as flow dependency errors

   --  Used to categorize warnings that are not issued by proof or flow
   --  analysis.
   type Misc_Warning_Kind is
     (Warn_Address_To_Access,
      Warn_Alias_Atomic_Vol,
      Warn_Alias_Different_Volatility,
      Warn_Attribute_Valid,
      Warn_Initialization_To_Alias,
      Warn_Function_Is_Valid,
      Warn_Lemma_Procedure_No_Return,
      Warn_Pragma_Annotate_No_Check,
      Warn_Pragma_Annotate_Proved_Check,
      Warn_Pragma_Annotate_Terminating,
      Warn_Pragma_External_Axiomatization,
      Warn_Pragma_Ignored,
      Warn_Pragma_Overflow_Mode,
      Warn_Precondition_Statically_False,
      Warn_Unreferenced_Function,
      Warn_Unreferenced_Procedure,
      Warn_Useless_Always_Return_Fun,
      Warn_Useless_Always_Return_Lemma,
      Warn_Useless_Relaxed_Init_Fun,
      Warn_Useless_Relaxed_Init_Obj,
      Warn_Variant_Not_Recursive,

      --  Warnings guaranteed to be issued
      Warn_Address_Atomic,
      Warn_Address_Valid,
      Warn_Assumed_Always_Return,
      Warn_Assumed_Global_Null,
      Warn_Assumed_Volatile_Properties,
      Warn_Indirect_Writes_Through_Alias,
      Warn_Indirect_Writes_To_Alias,

      --  Warnings only issued when using switch --pedantic
      Warn_Image_Attribute_Length,
      Warn_Operator_Reassociation,
      Warn_Representation_Attribute_Value
      );

   Max_Array_Dimensions : constant Positive := 4;
   --  Maximal number of array dimensions that are currently supported

   --  Used to categorize constructs which are not supported currently by the
   --  tool.
   type Unsupported_Kind is
     (Lim_Abstract_State_Part_Of_Concurrent_Obj,
      Lim_Access_Attr_With_Ownership_In_Unsupported_Context,
      Lim_Access_Conv,
      Lim_Access_Sub_Formal_With_Inv,
      Lim_Access_Sub_Protected,
      Lim_Access_Sub_Return_Type_With_Inv,
      Lim_Access_Sub_Traversal,
      Lim_Access_To_Dispatch_Op,
      Lim_Access_To_Relaxed_Init_Subp,
      Lim_Address_Attr_In_Unsupported_Context,
      Lim_Array_Conv_Different_Size_Modular_Index,
      Lim_Array_Conv_Signed_Modular_Index,
      Lim_Borrow_Traversal_First_Param,
      Lim_Borrow_Traversal_Volatile,
      Lim_Class_Attr_Of_Constrained_Type,
      Lim_Classwide_With_Predicate,
      Lim_Complex_Raise_Expr_In_Prec,
      Lim_Constrained_Classwide,
      Lim_Contract_On_Derived_Private_Type,
      Lim_Conv_Fixed_Float,
      Lim_Conv_Fixed_Integer,
      Lim_Conv_Float_Modular_128,
      Lim_Conv_Incompatible_Fixed,
      Lim_Deep_Object_With_Addr,
      Lim_Entry_Family,
      Lim_Exceptional_Cases_Dispatch,
      Lim_Exceptional_Cases_Ownership,
      Lim_Ext_Aggregate_With_Type_Ancestor,
      Lim_Goto_Cross_Inv,
      Lim_Img_On_Non_Scalar,
      Lim_Interpolated_String_Literal,
      Lim_Iterated_Element_Association,
      Lim_Iterator_In_Component_Assoc,
      Lim_Limited_Type_From_Limited_With,
      Lim_Loop_With_Iterator_Filter,
      Lim_Max_Array_Dimension,
      Lim_Max_Modulus,
      Lim_Move_To_Access_Constant,
      Lim_No_Return_Function,
      Lim_Non_Static_Attribute,
      Lim_Multiple_Inheritance_Interfaces,
      Lim_Multiple_Inheritance_Root,
      Lim_Multidim_Iterator,
      Lim_Multidim_Update,
      Lim_Object_Before_Inv,
      Lim_Op_Fixed_Float,
      Lim_Op_Incompatible_Fixed,
      Lim_Overlay_With_Deep_Object,
      Lim_Package_Before_Inv,
      Lim_Predicate_With_Different_SPARK_Mode,
      Lim_Primitive_Call_In_DIC,
      Lim_Protected_Operation_Of_Component,
      Lim_Protected_Operation_Of_Formal,
      Lim_Refined_Post_On_Entry,
      Lim_Relaxed_Init_Access_Type,
      Lim_Relaxed_Init_Aliasing,
      Lim_Relaxed_Init_Concurrent_Type,
      Lim_Relaxed_Init_Invariant,
      Lim_Relaxed_Init_Part_Of_Variable,
      Lim_Relaxed_Init_Protected_Component,
      Lim_Relaxed_Init_Tagged_Type,
      Lim_Relaxed_Init_Variant_Part,
      Lim_Subprogram_Before_Inv,
      Lim_Suspension_On_Formal,
      Lim_Target_Name_In_Borrow,
      Lim_Target_Name_In_Move,
      Lim_Type_Inv_Access_Type,
      Lim_Type_Inv_Nested_Package,
      Lim_Type_Inv_Private_Child,
      Lim_Type_Inv_Protected_Type,
      Lim_Type_Inv_Tagged_Comp,
      Lim_Type_Inv_Tagged_Type,
      Lim_Type_Inv_Volatile,
      Lim_Uninit_Alloc_In_Expr_Fun,
      Lim_Unknown_Alignment,
      Lim_UU_Tagged_Comp
      );

   subtype Default_Warning_Kind is Misc_Warning_Kind range
     Warn_Address_To_Access .. Warn_Variant_Not_Recursive;

   subtype Guaranteed_Warning_Kind is Misc_Warning_Kind range
     Warn_Address_Atomic .. Warn_Indirect_Writes_To_Alias;

   subtype Pedantic_Warning_Kind is Misc_Warning_Kind range
     Warn_Image_Attribute_Length .. Warn_Representation_Attribute_Value;

   --  Each warning kind is either a default or a pedantic one
   pragma Assert (for all Kind in Misc_Warning_Kind =>
                    (if Kind in Default_Warning_Kind then 1 else 0)
                  + (if Kind in Guaranteed_Warning_Kind then 1 else 0)
                  + (if Kind in Pedantic_Warning_Kind then 1 else 0)
                  = 1);

   function Warning_Message (Kind : Misc_Warning_Kind) return String is
     (case Kind is
        when Warn_Address_To_Access =>
          "?call to & is assumed to return a valid access"
          & " designating a valid value",
        when Warn_Alias_Atomic_Vol =>
          "?aliased objects must have the same volatility and atomic status",
        when Warn_Alias_Different_Volatility =>
          "?aliased objects have different volatile properties",
        when Warn_Attribute_Valid =>
          "?attribute Valid is assumed to return True",
        when Warn_Indirect_Writes_To_Alias =>
          "?writing to & is assumed to have no effects on"
          & " other non-volatile objects",
        when Warn_Initialization_To_Alias =>
          "?initialization of & is assumed to have no effects on"
          & " other non-volatile objects",
        when Warn_Function_Is_Valid =>
          "?function Is_Valid is assumed to return True",
        when Warn_Lemma_Procedure_No_Return =>
          "?lemma procedure cannot be instantiated automatically",
        when Warn_Pragma_Annotate_No_Check =>
          "?no check message justified by this pragma",
        when Warn_Pragma_Annotate_Proved_Check =>
          "?only proved check messages justified by this pragma",
        when Warn_Pragma_Annotate_Terminating =>
          "?Terminating annotations are deprecated",
        when Warn_Pragma_External_Axiomatization =>
          "?External Axiomatizations are not supported anymore, ignored",
        when Warn_Pragma_Ignored =>
          "?pragma % ignored (not yet supported)",
        when Warn_Pragma_Overflow_Mode =>
          "?pragma Overflow_Mode in code is ignored",
        when Warn_Precondition_Statically_False =>
          "?precondition is statically False",
        when Warn_Unreferenced_Function =>
          "?analyzing unreferenced function &",
        when Warn_Unreferenced_Procedure =>
          "?analyzing unreferenced procedure &",
        when Warn_Useless_Always_Return_Fun =>
          "?function & has implicit Always_Return annotation",
        when Warn_Useless_Always_Return_Lemma =>
          "?automatically instantiated lemma & has implicit Always_Return"
           & " annotation",
        when Warn_Useless_Relaxed_Init_Fun =>
          "?the result of & cannot be partially initialized",
        when Warn_Useless_Relaxed_Init_Obj =>
          "?& cannot be partially initialized",
        when Warn_Variant_Not_Recursive =>
          "?no recursive call visible",

        --  Warnings guaranteed to be issued
        when Warn_Address_Atomic =>
          "?assuming no concurrent accesses to non-atomic object &",
        when Warn_Address_Valid =>
          "?assuming valid reads from object &",
        when Warn_Assumed_Always_Return =>
          "?no returning annotation available for &",
        when Warn_Assumed_Global_Null =>
          "?no Global contract available for &",
        when Warn_Assumed_Volatile_Properties =>
          "?assuming correct volatile properties for &",
        when Warn_Indirect_Writes_Through_Alias =>
          "?indirect writes to & through a potential alias are ignored",

        --  Warnings only issued when using switch --pedantic
        when Warn_Image_Attribute_Length =>
          "?attribute % has an implementation-defined length",
        when Warn_Operator_Reassociation =>
          "?possible reassociation due to missing parentheses",
        when Warn_Representation_Attribute_Value =>
          "?attribute % has an implementation-defined value"
     );

   function Unsupported_Message
     (Kind : Unsupported_Kind;
      Name : String := "") return String is
     (case Kind is
         when Lim_Abstract_State_Part_Of_Concurrent_Obj =>
           "abstract state Part_Of constituent of a single concurrent object",
         when Lim_Access_Attr_With_Ownership_In_Unsupported_Context =>
           """Access"" attribute of a type with ownership not directly inside"
          & " an assignment statement, an object declaration, or a simple"
          & " return statement",
         when Lim_Access_Conv =>
           "implicit conversion between access types with different"
          & " designated types",
         when Lim_Access_Sub_Formal_With_Inv =>
           "formal with type invariants in access-to-subprogram",
         when Lim_Access_Sub_Protected =>
           "access to protected subprogram",
         when Lim_Access_Sub_Return_Type_With_Inv =>
           "access-to-subprogram returning a type with invariants",
         when Lim_Access_Sub_Traversal =>
           "access to borrowing traversal function",
         when Lim_Access_To_Dispatch_Op =>
           "access to dispatching operation",
         when Lim_Access_To_Relaxed_Init_Subp =>
           "access to subprogram annotated with Relaxed_Initialization",
         when Lim_Address_Attr_In_Unsupported_Context =>
           "attribute ""Address"" in unsupported context",
         when Lim_Object_Before_Inv =>
           "non-scalar object declared before loop-invariant",
         when Lim_Package_Before_Inv =>
           "nested packages before loop-invariant",
         when Lim_Subprogram_Before_Inv =>
           "nested subprogram before loop-invariant",
         when Lim_Goto_Cross_Inv =>
           "goto statement to label located inside the loop crossing the loop"
          & " invariant",
         when Lim_Multidim_Update =>
           "attribute ""Update"" of unconstrained multidimensional array",
         when Lim_Uninit_Alloc_In_Expr_Fun =>
           "uninitialized allocator inside expression function",
         when Lim_Iterator_In_Component_Assoc =>
           "iterated component association with iterator specification",
         when Lim_Exceptional_Cases_Dispatch =>
           "aspect ""Exceptional_Cases"" on dispatching operation",
         when Lim_Exceptional_Cases_Ownership =>
           "procedures with exceptional contracts and parameters of mode"
          & " ""in out"" or ""out"" subjected to ownerhsip which might not be "
          & "passed by reference",
         when Lim_Ext_Aggregate_With_Type_Ancestor =>
           "extension aggregate with subtype ancestor part",
         when Lim_Iterated_Element_Association =>
           "iterated element association",
         when Lim_Multidim_Iterator =>
           "iterator specification over multi-dimensional array",
         when Lim_Loop_With_Iterator_Filter =>
           "loop on an iterator specification with an iterator filter",
         when Lim_Complex_Raise_Expr_In_Prec =>
           "raise expression in a complex expression in a precondition",
         when Lim_Array_Conv_Different_Size_Modular_Index =>
           "conversion between array types with modular index types of"
          & " different sizes",
         when Lim_Array_Conv_Signed_Modular_Index =>
           "conversion between array types with modular and non-modular index"
          & " types",
         when Lim_Move_To_Access_Constant =>
           "move as part of a conversion to an access-to-constant type",
         when Lim_Conv_Fixed_Float =>
           "conversion between fixed-point and floating-point types",
         when Lim_Conv_Incompatible_Fixed =>
           "conversion between incompatible fixed-point types",
         when Lim_Conv_Fixed_Integer =>
           "conversion between fixed-point and integer types",
         when Lim_Conv_Float_Modular_128 =>
           "conversion between floating-point and 128-bits modular types",
         when Lim_Target_Name_In_Borrow =>
           "'@ inside a reborrow",
         when Lim_Target_Name_In_Move =>
           "'@ inside a move assignment",
         when Lim_Deep_Object_With_Addr =>
           "address clause on an object of an ownership type",
         when Lim_Overlay_With_Deep_Object =>
           "overlay with an object of an ownership type",
         when Lim_Non_Static_Attribute =>
           "non-static attribute """ & Standard_Ada_Case (Name) & """",
         when Lim_Img_On_Non_Scalar =>
           "attribute """ & Standard_Ada_Case (Name) & """ on non-scalar type",
         when Lim_Interpolated_String_Literal =>
           "interpolated string literal",
         when Lim_Unknown_Alignment =>
           "unknown value of object alignment",
         when Lim_Op_Fixed_Float =>
           "operation between fixed-point and floating-point types",
         when Lim_Op_Incompatible_Fixed =>
           "operation between incompatible fixed-point types",
         when Lim_Protected_Operation_Of_Formal =>
           "call to operation of a formal protected parameter",
         when Lim_Protected_Operation_Of_Component =>
           "call to operation of a component of a protected type",
         when Lim_Suspension_On_Formal =>
           "suspension on a formal parameter",
         when Lim_Borrow_Traversal_First_Param =>
           "borrowing traversal functions whose first parameter does not have"
          & " an anonymous access-to-variable type",
         when Lim_Borrow_Traversal_Volatile =>
           "volatile borrowing traversal function",
         when Lim_No_Return_Function =>
           "function annotated with No_Return",
         when Lim_Multiple_Inheritance_Root =>
           "subprogram inherited from root and interface",
         when Lim_Multiple_Inheritance_Interfaces =>
           "subprogram inherited from multiple interfaces",
         when Lim_Primitive_Call_In_DIC =>
           "primitive calls in default initial condition",
         when Lim_Constrained_Classwide =>
           "constrained class-wide subtype",
         when Lim_Type_Inv_Access_Type =>
           "access to incomplete or private type which needs an invariant"
          & " check",
         when Lim_Type_Inv_Nested_Package =>
           "type invariant in a nested package",
         when Lim_Type_Inv_Private_Child =>
           "type invariant in private child unit",
         when Lim_Type_Inv_Protected_Type =>
           "type invariant on protected types",
         when Lim_Type_Inv_Tagged_Type =>
           "type invariant on tagged types",
         when Lim_Type_Inv_Volatile =>
           "volatile object with asynchronous writers or readers and a type"
          & " invariant",
         when Lim_Type_Inv_Tagged_Comp =>
           "type invariant on components of tagged types",
         when Lim_Max_Array_Dimension =>
            "array of dimension greater than" & Max_Array_Dimensions'Img,
         when Lim_Max_Modulus =>
            "modulus greater than 2 '*'* 128",
         when Lim_Class_Attr_Of_Constrained_Type =>
            "attribute ""Class"" of a constrained type",
         when Lim_Classwide_With_Predicate =>
           "subtype predicate on a classwide type",
         when Lim_Contract_On_Derived_Private_Type =>
           "type aspect on type derived from a private type",
         when Lim_Predicate_With_Different_SPARK_Mode =>
           "type with predicates with different SPARK_Mode values",
         when Lim_UU_Tagged_Comp =>
           "component of an unconstrained unchecked union type in a tagged"
          & " extension",
         when Lim_Relaxed_Init_Protected_Component =>
           "protected component with relaxed initialization",
         when Lim_Relaxed_Init_Part_Of_Variable =>
           "variable annotated as Part_Of a concurrent object with relaxed"
          & " initialization",
         when Lim_Relaxed_Init_Invariant =>
           "invariant on a type used as a subcomponent of a type or"
          & " an object annotated with relaxed initialization",
         when Lim_Relaxed_Init_Tagged_Type =>
           "tagged type used as a subcomponent of a type or"
          & " an object annotated with relaxed initialization",
         when Lim_Relaxed_Init_Access_Type =>
           "access type used as a subcomponent of a type or"
          & " an object annotated with relaxed initialization",
         when Lim_Relaxed_Init_Aliasing =>
           "relaxed initialization on overlaid objects",
         when Lim_Relaxed_Init_Concurrent_Type =>
           "concurrent type used as a subcomponent of a type or"
          & " an object annotated with relaxed initialization",
         when Lim_Relaxed_Init_Variant_Part =>
            "subtype with a discriminant constraint containing only"
          & " subcomponents whose type is annotated with"
          & " Relaxed_Initialization",
         when Lim_Limited_Type_From_Limited_With =>
           "limited view of type & coming from limited with",
         when Lim_Refined_Post_On_Entry =>
           "Refined_Post aspect on a protected entry",
         when Lim_Entry_Family =>
           "entry family"
     );

   function CWE_ID (Kind : VC_Kind) return String;
   function CWE_ID (Kind : Valid_Flow_Tag_Kind) return String;
   --  Return the CWE number for a given kind as a string; return the empty
   --  string if the Kind has no associated CWE.

   function CWE_Message (Kind : VC_Kind) return String;
   function CWE_Message (Kind : Valid_Flow_Tag_Kind) return String;
   --  Return the CWE number for a given kind as a nice string "[CWE
   --  <number>]"; return the empty string if the Kind has no associated CWE.

   function Description (Kind : VC_Kind) return String;
   function Description (Kind : Valid_Flow_Tag_Kind) return String;
   function Description (Kind : Misc_Warning_Kind) return String;
   function Description (Kind : Unsupported_Kind) return String;
   --  Return a one-line description for each kind of message as a string

   function Kind_Name (Kind : VC_Kind) return String;
   function Kind_Name (Kind : Valid_Flow_Tag_Kind) return String;
   function Kind_Name (Kind : Misc_Warning_Kind) return String;
   --  Return a short string for each kind of message as a string, e.g. "index
   --  check" for VC_Index_Check.

   function Rule_Name (Kind : VC_Kind) return String;
   function Rule_Name (Kind : Valid_Flow_Tag_Kind) return String;
   --  Return a tag for each kind of message that is used to identify the
   --  string e.g. in the GPS plug-in.

   function Locate_On_First_Token (V : VC_Kind) return Boolean is
     (case V is when VC_RTE_Kind     => False,
                when VC_Assert_Kind  => V not in VC_Precondition | VC_Raise,
                when VC_LSP_Kind     => True,
                when VC_Warning_Kind => True);
   --  Returns True if this kind of VC should be considered like an assertion
   --  when positioning the message to the left-most subexpression of the
   --  checked expression. For example, this is not true for VC_Precondition,
   --  which should be positioned on the location of the call.

   type Analysis_Progress is
     (Progress_None,
      Progress_Marking,
      Progress_Borrow,
      Progress_Flow,
      Progress_Proof);
   pragma Ordered (Analysis_Progress);
   --  Indicates the last phase that was completed during analysis. Note
   --  that borrow checking appears before flow analysis, even though borrow
   --  checking is done afterwards. This is to reflect the user view, where
   --  borrow checking is essentially an extension of marking.

   type Stop_Reason_Type is
     (Stop_Reason_None,
      Stop_Reason_Generic_Unit,    --  The unit is a generic unit
      Stop_Reason_Check_Mode,      --  Only check mode was requested
      Stop_Reason_Flow_Mode,       --  Only flow analysis was requested
      Stop_Reason_Error_Marking,   --  Error during marking
      Stop_Reason_Error_Flow,      --  Error during flow
      Stop_Reason_Error_Borrow);   --  Error during borrow checking
   --  Indicates why the analysis did not progress to the next phase

   SPARK_Suffix : constant String := "spark";
   --  Extension of the files where spark_report expects gnat2why results

   type SPARK_Mode_Status is
     (All_In_SPARK,       --  Spec (and if applicable, body) are in SPARK
      Spec_Only_In_SPARK, --  Only spec is in SPARK, body is not in SPARK
      Not_In_SPARK);      --  Not in SPARK

   ------------
   -- Labels --
   ------------

   --  These strings are used in Why3 labels to communicate information to
   --  Why3. Changes here should be propagated to the code of gnatwhy3. In
   --  gnat2why, use of the corresponding Name_Ids in Why.Atree.Modules is
   --  preferred over using the strings here.

   GP_Check_Marker          : constant String := "GP_Check:";
   GP_Pretty_Ada_Marker     : constant String := "GP_Pretty_Ada:";
   GP_Shape_Marker          : constant String := "GP_Shape:";
   GP_Inline_Marker         : constant String := "GP_Inline";
   GP_Inlined_Marker        : constant String := "GP_Inlined";

   --  A few labels are used in Why3 to identify variables and terms whose
   --  value is interesting in counter-examples.

   Model_Trace_Label   : constant String := "model_trace:";
   Model_Proj_Label    : constant String := "model_projected";
   VC_Annotation_Label : constant String := "vc:annotation";
   Model_VC_Post_Label : constant String := "model_vc_post";
   Branch_Id_Label     : constant String := "branch_id=";
   RAC_Assume_Label    : constant String := "RAC:assume";
   --  When a logical annotation is a conjunction and is checked during
   --  RAC, conjuncts marked by this label are assumed to be true.

   Model_Proj_Meta : constant String := "model_projection";
   --  A meta that is used in Why3 to mark a function as projection.

   --  Constants that are used in the extra_info returned from gnatwhy3, to
   --  identify lower and upper bound of a range check.

   Low_Bound_Id  : constant Integer := -1;
   High_Bound_Id : constant Integer := -2;

   --------------------
   --  Data Exchange --
   --------------------

   --  This section defines various types that are used to communicate between
   --  the various gnatprove processes (most notably between gnat2why/gnatwhy3
   --  and gnat2why/spark_report). Also, JSON conversion functions are defined.

   type Prover_Stat is record
      Count     : Natural;
      Max_Steps : Natural;
      Max_Time  : Float;
   end record;

   package Prover_Stat_Maps is new
     Ada.Containers.Indefinite_Ordered_Maps (Key_Type     => String,
                                             Element_Type => Prover_Stat,
                                             "<"          => "<",
                                             "="          => "=");
   --  The prover stats JSON format is defined in gnat_report.mli

   type Prover_Category is (PC_Trivial, PC_Prover, PC_Flow);
   --  Type that describes the possible ways a check is proved. PC_Prover
   --  stands for automatic or manual proofs from Why3 and does not specify
   --  which prover proves it.
   --  PC_Trivial is used here for any "proofs" that come from gnat2why. For
   --  checks that are proved by a transformation in gnatwhy3, PC_Prover is
   --  used with a prover of name "Trivial". The distinction is necessary in
   --  some cases (e.g. to avoid redoing checks in why3). The two notions are
   --  merged by spark_report to present a single "Trivial" prover to the user.

   type CEE_Kind is (CEE_Variable,
                     CEE_Error_Msg,
                     CEE_Old,
                     CEE_Result,
                     CEE_Other);

   type Cntexmp_Type is
     (Cnt_Integer,
      Cnt_Decimal,
      Cnt_Float,
      Cnt_Boolean,
      Cnt_Bitvector,
      Cnt_Array,
      Cnt_Record,
      Cnt_Projection,
      Cnt_Invalid);
   --  Counterexamples are typed.
   --  Matching on this types in the code should make debugging easier.
   --  Without this we would only be manipulating Unbounded_String which
   --  is not usable.

   --  Enumeration of possible float values in float counterex.
   type Float_Type is
     (Float_Plus_Infinity,
      Float_Minus_Infinity,
      Float_Plus_Zero,
      Float_Minus_Zero,
      Float_NaN,
      Float_Val);

   --  Record for float types
   type Float_Value (F_Type : Float_Type) is record
      case F_Type is
         when Float_Plus_Infinity
            | Float_Minus_Infinity
            | Float_Plus_Zero
            | Float_Minus_Zero
            | Float_NaN => null;
         when Float_Val =>
            F_Sign        : Unbounded_String;
            F_Exponent    : Unbounded_String;
            F_Significand : Unbounded_String;
      end case;
   end record;

   type Float_Value_Ptr is not null access constant Float_Value;

   type Cntexmp_Value;
   type Cntexmp_Value_Ptr is access constant Cntexmp_Value;

   package Cntexmp_Value_Array is
      new Ada.Containers.Indefinite_Ordered_Maps
       (Key_Type     => String, -- Indices can exceed MAX_INT
        Element_Type => Cntexmp_Value_Ptr);
   --  Map of counterexample values.
   --  In the case of counterexample array, the Key_Type represents the index.

   type Cntexmp_Value (T : Cntexmp_Type := Cnt_Invalid) is record
      case T is
         when Cnt_Integer    => I  : Unbounded_String;
         when Cnt_Decimal    => D  : Unbounded_String;
         when Cnt_Float      => F  : Float_Value_Ptr;
         when Cnt_Boolean    => Bo : Boolean;
         when Cnt_Bitvector  => B  : Unbounded_String;
         when Cnt_Record     =>
            Fi : Cntexmp_Value_Array.Map;
         when Cnt_Projection => Er : Unbounded_String;
            --  Cnt_projection is an error case anywhere after vc_kinds
         when Cnt_Array      =>
            Array_Indices : Cntexmp_Value_Array.Map;
            Array_Others  : Cntexmp_Value_Ptr;
         when Cnt_Invalid    => S  : Unbounded_String;
      end case;
   end record;
   --  Counterexample values
   --
   --  This record should be changed to take more precise type into account.
   --  For example, floats are actually the concatenation of two numbers "d.n"
   --  This is present in why3 and can be mimicked in SPARK.

   package S_String_List is new
     Ada.Containers.Indefinite_Doubly_Linked_Lists
       (Element_Type => Unbounded_String,
        "="          => "=");

   type CNT_Unbounded_String is record
      Str   : Unbounded_String;
      Count : Natural := 0;
      Elems : S_String_List.List;
   end record
     with Predicate => Count >= Natural (Elems.Length);
   --  Mostly a string for a counterexample value. Component Count
   --  gives the number of individual subcomponents being printed in Str, and
   --  component Elems gives the value of individual non-others non-nul
   --  subcomponents, to be used if the Count is too large for printing Str.

   type Cntexample_Kind is (Raw, Pretty_Printed);

   type Cntexample_Elt (K : Cntexample_Kind := Raw) is record
      Kind    : CEE_Kind;
      Name    : Unbounded_String;
      case K is
         when Raw =>
            Labels : S_String_List.List;
            Value  : Cntexmp_Value_Ptr;
         when Pretty_Printed =>
            Val_Str : CNT_Unbounded_String;
      end case;
   end record;

   package Cntexample_Elt_Maps is new
     Ada.Containers.Indefinite_Ordered_Maps (Key_Type     => String,
                                             Element_Type => Cntexample_Elt,
                                             "<"          => "<",
                                             "="          => "=");

   function Eq_List (A, B : Cntexample_Elt) return Boolean is
      (A.Name = B.Name);

   package Cntexample_Elt_Lists is new
     Ada.Containers.Doubly_Linked_Lists (Element_Type => Cntexample_Elt,
                                         "="          => Eq_List);

   package Cntexample_Line_Maps is new
     Ada.Containers.Ordered_Maps (Key_Type     => Natural,
                                  Element_Type => Cntexample_Elt_Lists.List,
                                  "<"          => "<",
                                  "="          => Cntexample_Elt_Lists."=");

   type Previous_Line is record
      Line_Cnt : Cntexample_Elt_Lists.List;
      Ada_Node : Integer;  --  Node_Id of the Loop_Invariant
   end record;

   function Eq_previous (A, B : Previous_Line) return Boolean is
      (Cntexample_Elt_Lists."=" (A.Line_Cnt, B.Line_Cnt));

   package Previous_Line_Maps is new
     Ada.Containers.Ordered_Maps (Key_Type     => Natural,
                                  Element_Type => Previous_Line,
                                  "<"          => "<",
                                  "="          => Eq_previous);

   type Cntexample_Lines is record
      VC_Line        : Cntexample_Elt_Lists.List;
      --  Counterexamples on the VC line
      Other_Lines    : Cntexample_Line_Maps.Map;
      --  Counterexamples on all other lines
      Previous_Lines : Previous_Line_Maps.Map;
      --  Additional counterexamples for the previous lines
   end record;
   --  Previous lines is a feature related to loops. For Why3, intuitively, the
   --  check inside the loop assumes the loop invariant at previous iterations.
   --  So, when a counterexample appears, it contains the values at "previous
   --  iteration". These values have their locations duplicated by the VC
   --  generation exactly at the location of the while line (in Why3). So, what
   --  has been done here, is to change the location of loops to a recognizable
   --  one. These counterexamples are generated at these locations in the first
   --  pass and in the second pass (now), we recognize them to display them
   --  specially (with "Previous iteration" text).

   package Cntexample_File_Maps is new
     Ada.Containers.Indefinite_Ordered_Maps (Key_Type     => String,
                                             Element_Type => Cntexample_Lines,
                                             "<"          => "<",
                                             "="          => "=");

   type Cntexmp_Verdict_Category is
     (Non_Conformity,
      --  The counterexample shows how the code contradicts the check
      Subcontract_Weakness,
      --  The counterexample shows how some sub-contracts are too weak to
      --  prove the check
      Non_Conformity_Or_Subcontract_Weakness,
      --  Either of the above
      Bad_Counterexample,
      --  The counterexample is bad, e.g. it contains values that contradict
      --  the preconditions, or the RAC based on the counterexample doesn't
      --  fail or it fails at a different check
      Incomplete,
      --  The counterexample could not be checked (e.g., RAC implementation is
      --  incomplete, check could not be validated, RAC took too much time)
      Not_Checked
      --  Counterexample checking was not requested
     );
   --  The different categories when checking the counterexample for a check.

   subtype Cntexmp_Confirmed_Verdict_Category is Cntexmp_Verdict_Category
   range Non_Conformity .. Non_Conformity_Or_Subcontract_Weakness;
   --  The categories of confirmed counterexamples

   type Cntexmp_Verdict
     (Verdict_Category : Cntexmp_Verdict_Category := Not_Checked)
   is
      record
         case Verdict_Category is
         when Bad_Counterexample
            | Incomplete
            | Not_Checked
         =>
            Verdict_Reason : Unbounded_String :=
                               To_Unbounded_String ("Unknown");
         when Cntexmp_Confirmed_Verdict_Category =>
            null;
         end case;
      end record;
   --  The result when checking the counterexample for a check, based on Why3
   --  giant-step RAC and SPARK small-step RAC.

   function Reason (Verdict : Cntexmp_Verdict) return String is
     (case Verdict.Verdict_Category is
         when Bad_Counterexample | Not_Checked | Incomplete =>
            To_String (Verdict.Verdict_Reason),
         when others                                        =>
            "");
   --  Return the reason for a verdict (empty for confirmed verdicts)

   function To_String (P : Prover_Category) return String;
   --  Return a user-visible string to describe the category of prover

   function From_JSON (V : JSON_Value) return Prover_Stat;
   function From_JSON (V : JSON_Value) return Prover_Stat_Maps.Map;
   function From_JSON (V : JSON_Value) return Prover_Category;
   function From_JSON (V : JSON_Value) return Cntexample_File_Maps.Map;
   function From_JSON (V : JSON_Value) return SPARK_Mode_Status;

   function From_JSON_Labels (Ar : JSON_Array) return S_String_List.List;

   function To_JSON (M : Prover_Stat_Maps.Map) return JSON_Value;
   function To_JSON (P : Prover_Category) return JSON_Value;
   function To_JSON (F : Cntexample_File_Maps.Map) return JSON_Value;
   function To_JSON (V : Cntexmp_Value) return JSON_Value;
   function To_JSON (Status : SPARK_Mode_Status) return JSON_Value;
end VC_Kinds;
