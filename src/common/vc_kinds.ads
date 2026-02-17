------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                              V C _ K I N D S                             --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2026, AdaCore                     --
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
with Ada.Strings.Fixed;     use Ada.Strings.Fixed;
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

      VC_Predicate_Check_On_Default_Value,
      --  The predicate check on the default value of a type, to be used when a
      --  value of the type is default initialized.

      VC_Null_Pointer_Dereference,
      --  This VC is to be used whenever we try to dereference an object with
      --  access type. This check should be done on the _is_null_pointer field
      --  of the why record corresponding to the pointer type.

      VC_Null_Exclusion,
      VC_Dynamic_Accessibility_Check,
      VC_Resource_Leak,
      VC_Resource_Leak_At_End_Of_Scope,

      VC_Unchecked_Union_Restriction,
      --  Specific restrictions for types with Unchecked_Union occuring in
      --  equality, membership tests, and type conversions.

      VC_Length_Check,
      VC_Discriminant_Check,
      VC_Tag_Check,
      VC_Ceiling_Interrupt,
      VC_Initialization_Check,
      VC_Validity_Check,
      VC_Interrupt_Reserved,
      VC_Invariant_Check,

      VC_Invariant_Check_On_Default_Value,
      --  The invariant check on the default value of a type, it is used once
      --  at the type declaration.

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
      VC_Disjoint_Cases,
      VC_Complete_Cases,
      VC_Exceptional_Case,
      VC_Exit_Case,

      VC_Loop_Invariant,
      --  Internal check kind, transformed by gnatwhy3 into
      --  VC_Loop_Invariant_Init or VC_Loop_Invariant_Preserv.

      VC_Loop_Invariant_Init,
      VC_Loop_Invariant_Preserv,
      VC_Loop_Variant,
      VC_Program_Exit_Post,
      VC_Subprogram_Variant,
      VC_Assert,
      VC_Assert_Step,                --  Side condition for proof cut points
      VC_Assert_Premise,             --  Premise for proof with cut points
      VC_Raise,
      VC_Unexpected_Program_Exit,

      VC_Feasible_Post,
      --  Check that the postcondition of abstract functions and
      --  access-to-function types are feasible.

      VC_Inline_Check,
      --  Check that the Inline_For_Proof or Logical_Equal annotation provided
      --  for a function is correct.

      VC_Container_Aggr_Check,
      --  Check that the Container_Aggregates annotation provided for a
      --  container type is correct.

      VC_Reclamation_Check,
      --  Check that confirming annotations on hidden types which need
      --  reclamation are correct.

      VC_Termination_Check,
      --  Check conditional termination.

      VC_UC_Source,
      --  Check that this type is suitable as a source for an
      --  Unchecked_Conversion.

      VC_UC_Target,
      --  Check that this type is suitable as a target for an
      --  Unchecked_Conversion.

      VC_UC_Same_Size,
      --  Check that the two types of an Unchecked_Conversion are of the same
      --  size.

      VC_UC_Align_Overlay,
      --  Check that the address in an address clause respect object alignment

      VC_UC_Align_UC,
      --  Check alignment constring for Unchecked_Conversion

      VC_UC_Volatile,
      --  Check that we specify the address of an object only if it is
      --  volatile, or the address clause is "simple".

      --  VC_LSP_Kind - Liskov Substitution Principle

      VC_Weaker_Pre,
      --  pre weaker than classwide pre

      VC_Trivial_Weaker_Pre,
      --  specialization of VC_Weaker_Pre when there is no classwide or
      --  inherited precondition

      VC_Stronger_Post,               --  post stronger than classwide post
      VC_Weaker_Classwide_Pre,        --  classwide pre weaker than inherited
      VC_Stronger_Classwide_Post,     --  classwide post stronger t/ inherited

      VC_Weaker_Pre_Access,
      --  pre of source is weaker than pre of target.

      VC_Stronger_Post_Access,
      --  post of source is stronger than post of target.

      --  VC_Warning_Kind - warnings

      VC_Inconsistent_Pre,
      VC_Inconsistent_Post,
      VC_Inconsistent_Assume,
      VC_Unreachable_Branch,
      VC_Dead_Code);

   subtype VC_Overflow_Kind is
     VC_Kind range VC_Overflow_Check .. VC_FP_Overflow_Check;

   subtype VC_Range_Kind is VC_Kind
   with
     Static_Predicate =>
       VC_Range_Kind
       in VC_Overflow_Check
        | VC_FP_Overflow_Check
        | VC_Range_Check
        | VC_Length_Check
        | VC_Index_Check;

   subtype VC_RTE_Kind is
     VC_Kind range VC_Division_Check .. VC_Task_Termination;

   subtype VC_Assert_Kind is
     VC_Kind range VC_Initial_Condition .. VC_UC_Volatile;

   subtype VC_LSP_Kind is
     VC_Kind range VC_Weaker_Pre .. VC_Stronger_Post_Access;

   subtype VC_Warning_Kind is
     VC_Kind range VC_Inconsistent_Pre .. VC_Dead_Code;

   subtype Proof_High_Severity_Kind is VC_Kind
   with
     Predicate =>
       Proof_High_Severity_Kind
       in VC_UC_Source
        | VC_UC_Target
        | VC_UC_Same_Size
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
      --  A function with side effects has been found

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
      --  A ghost subprogram has a non-ghost global output

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
      --  A subprogram with aspect Always_Terminates may not terminate

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

   subtype Flow_Error_Kind is
     Flow_Tag_Kind range Critical_Global_Missing .. Side_Effects;

   subtype Flow_Check_Kind is Flow_Tag_Kind range Aliasing .. Unused_Global;

   subtype Flow_Warning_Kind is
     Flow_Tag_Kind
       range Dead_Code .. Volatile_Function_Without_Volatile_Effects;

   subtype Valid_Flow_Tag_Kind is
     Flow_Tag_Kind range Flow_Tag_Kind'Succ (Empty_Tag) .. Flow_Tag_Kind'Last;
   --  Non-empty tags

   --  Each valid flow analysis kind is exactly one of error/check/warning
   pragma
     Assert
       (for all Kind in Valid_Flow_Tag_Kind =>
          (if Kind in Flow_Error_Kind then 1 else 0)
          + (if Kind in Flow_Check_Kind then 1 else 0)
          + (if Kind in Flow_Warning_Kind then 1 else 0)
          = 1);

   subtype Data_Dependency_Tag is Flow_Tag_Kind
   with
     Static_Predicate =>
       Data_Dependency_Tag
       in Global_Missing
        | Global_Wrong
        | Export_Depends_On_Proof_In
        | Illegal_Update
        | Not_Constant_After_Elaboration;
   --  Tags reported as data dependency errors

   subtype Flow_Dependency_Tag is Flow_Tag_Kind
   with
     Static_Predicate =>
       Flow_Dependency_Tag
       in Depends_Null
        | Depends_Missing
        | Depends_Missing_Clause
        | Depends_Wrong
        | Initializes_Wrong;
   --  Tags reported as flow dependency errors

   --  Used to categorize warnings that are not issued by proof or flow
   --  analysis.
   type Misc_Warning_Kind is
     (Warn_Alias_Atomic_Vol,
      Warn_Alias_Different_Volatility,
      Warn_Attribute_Valid,
      Warn_Auto_Lemma_Calls,
      Warn_Auto_Lemma_Different,
      Warn_Auto_Lemma_Higher_Order,
      Warn_Auto_Lemma_Specializable,
      Warn_Initialization_To_Alias,
      Warn_Function_Is_Valid,
      Warn_Generic_Not_Analyzed,
      Warn_No_Possible_Termination,
      Warn_Potentially_Invalid_Read,
      Warn_Pragma_Annotate_No_Check,
      Warn_Pragma_Annotate_Proved_Check,
      Warn_Pragma_Annotate_Terminating,
      Warn_Pragma_External_Axiomatization,
      Warn_Pragma_Ignored,
      Warn_Pragma_Overflow_Mode,
      Warn_Precondition_Statically_False,
      Warn_Restriction_Ignored,
      Warn_Unreferenced_Function,
      Warn_Unreferenced_Procedure,
      Warn_Useless_Potentially_Invalid_Fun,
      Warn_Useless_Potentially_Invalid_Obj,
      Warn_Useless_Relaxed_Init_Fun,
      Warn_Useless_Relaxed_Init_Obj,
      Warn_Variant_Not_Recursive,

      --  Warnings guaranteed to be issued
      Warn_Address_To_Access,
      Warn_Assumed_Always_Terminates,
      Warn_Assumed_Global_Null,
      Warn_Imprecisely_Supported_Address,

      --  Warnings only issued when using switch --pedantic
      Warn_Image_Attribute_Length,
      Warn_Operator_Reassociation,
      Warn_Representation_Attribute_Value,

      --  Warnings only issued when using switch --info

      --  Tool limitations not impacting soundness

      Warn_Comp_Relaxed_Init,
      Warn_Full_View_Visible,

      --  Flow limitations not impacting soundness

      Warn_Alias_Array,
      Warn_Imprecise_GG,
      Warn_Init_Array,
      Warn_Init_Multidim_Array,
      Warn_Tagged_Untangling,

      --  Proof limitations not impacting soundness

      Warn_Contracts_Recursive,
      Warn_Proof_Module_Cyclic,
      Warn_DIC_Ignored,
      Warn_Imprecise_Address,
      Warn_Imprecise_Align,
      Warn_Imprecise_Call,
      Warn_Imprecise_String_Literal,
      Warn_Component_Size,
      Warn_Record_Component_Attr,
      Warn_Imprecise_Size,
      Warn_Imprecise_Overlay,
      Warn_Imprecise_UC,
      Warn_Imprecise_Value,
      Warn_Imprecise_Image,
      Warn_Loop_Entity,
      Warn_No_Reclam_Func,
      Warn_Relaxed_Init_Mutable_Discr,
      Warn_Map_Length_Aggregates,
      Warn_Set_Length_Aggregates,

      --  Other --info warnings

      Warn_Predef_Eq_Null,
      Warn_Init_Cond_Ignored,
      Warn_Unit_Not_SPARK,

      --  Info messages enabled by default
      Warn_Info_Unrolling_Inlining);

   --  TODO Warn_Unit_Not_SPARK should just be a regular warning.
   --  Warn_Info_Unrolling_Inlining is part of Warning enumeration as it can be
   --  disabled using the same mechanism.

   Max_Array_Dimensions : constant Positive := 4;
   --  Maximal number of array dimensions that are currently supported

   type Error_Message_Kind is
     (Err_Comp_Not_Present,

      --  Incorrect uses of pragma/aspect Annotate

      --  Common to all annotations

      Annot_Argument_Number,
      Annot_Bad_Entity,
      Annot_Duplicated_Annotated_Entity,
      Annot_Duplicated_Annotation,
      Annot_Entity_Expected,
      Annot_Entity_Placement,
      Annot_Function_Return_Type,
      Annot_Function_Traversal,
      Annot_Function_With_Side_Effects,
      Annot_Invalid_Name,
      Annot_Placement,
      Annot_Pragma_On_Generic,
      Annot_String_Third_Argument,
      Annot_Subp_Access_Global,
      Annot_Subp_Parameter_Number,
      Annot_Subp_Parameter_Type,
      Annot_Volatile_Function,
      Annot_Wrong_Third_Parameter,

      --  Specific to a kind of annotation

      Annot_At_End_Borrow_Context,
      Annot_At_End_Borrow_Param,
      Annot_At_End_Borrow_Param_In_Contract,
      Annot_Container_Aggregates_Add,
      Annot_Container_Aggregates_Add_Access_Param,
      Annot_Container_Aggregates_No_Aggregate,
      Annot_Container_Aggregates_Private,
      Annot_Handler_Call,
      Annot_Handler_Conversion,
      Annot_Hide_Info_Private_Child,
      Annot_Hide_Info_Private_Eq,
      Annot_Hide_Info_Private_Ownership,
      Annot_Inline_For_Proof_Body_Off,
      Annot_No_Bitwise_Operations_Use,
      Annot_Ownership_Potentially_Invalid,
      Annot_Predefined_Equality_Use_Eq,

      --  Language violations

      Vio_Access_Constant,
      Vio_Access_Expression,
      Vio_Access_Function_With_Side_Effects,
      Vio_Access_No_Root,
      Vio_Access_Subprogram_Within_Protected,
      Vio_Access_Sub_Formal_With_Inv,
      Vio_Access_Sub_Return_Type_With_Inv,
      Vio_Access_Sub_With_Globals,
      Vio_Access_To_Dispatch_Op,
      Vio_Access_Volatile_Function,
      Vio_Address_Of_Non_Object,
      Vio_Address_Outside_Address_Clause,
      Vio_Aggregate_Globals,
      Vio_Aggregate_Side_Effects,
      Vio_Aggregate_Volatile,
      Vio_Assert_And_Cut_Context,
      Vio_Backward_Goto,
      Vio_Box_Notation_Without_Init,
      Vio_Code_Statement,
      Vio_Controlled_Types,
      Vio_Container_Aggregate,
      Vio_Default_With_Current_Instance,
      Vio_Derived_Untagged_With_Tagged_Full_View,
      Vio_Discriminant_Access,
      Vio_Discriminant_Derived,
      Vio_Dispatch_Plain_Pre,
      Vio_Dispatching_Untagged_Type,
      Vio_Exit_Cases_Exception,
      Vio_Exit_Cases_Normal_Only,
      Vio_Function_Global_Output,
      Vio_Function_Out_Param,
      Vio_Ghost_Concurrent_Comp,
      Vio_Ghost_Eq,
      Vio_Ghost_Volatile,
      Vio_Handler_Choice_Parameter,
      Vio_Invariant_Class,
      Vio_Invariant_Ext,
      Vio_Invariant_Partial,
      Vio_Invariant_Volatile,
      Vio_Iterable_Controlling_Result,
      Vio_Iterable_Full_View,
      Vio_Iterable_Globals,
      Vio_Iterable_Side_Effects,
      Vio_Iterable_Volatile,
      Vio_Iterator_Specification,
      Vio_Loop_Variant_Structural,
      Vio_Overlay_Constant_Not_Imported,
      Vio_Overlay_Mutable_Constant,
      Vio_Overlay_Part_Of_Protected,
      Vio_Ownership_Access_Equality,
      Vio_Ownership_Allocator_Invalid_Context,
      Vio_Ownership_Allocator_Uninitialized,
      Vio_Ownership_Anonymous_Access_To_Named,
      Vio_Ownership_Anonymous_Part_Of,
      Vio_Ownership_Anonymous_Object_Context,
      Vio_Ownership_Anonymous_Object_Init,
      Vio_Ownership_Anonymous_Result,
      Vio_Ownership_Assign_To_Expr,
      Vio_Ownership_Assign_To_Constant,
      Vio_Ownership_Borrow_Of_Constant,
      Vio_Ownership_Borrow_Of_Non_Markable,
      Vio_Ownership_Anonymous_Component,
      Vio_Ownership_Deallocate_General,
      Vio_Ownership_Different_Branches,
      Vio_Ownership_Duplicate_Aggregate_Value,
      Vio_Ownership_Loop_Entry_Old_Copy,
      Vio_Ownership_Loop_Entry_Old_Traversal,
      Vio_Ownership_Move_Constant_Part,
      Vio_Ownership_Move_In_Declare,
      Vio_Ownership_Move_Not_Name,
      Vio_Ownership_Move_Traversal_Call,
      Vio_Ownership_Reborrow,
      Vio_Ownership_Storage_Pool,
      Vio_Ownership_Tagged_Extension,
      Vio_Ownership_Traversal_Extended_Return,
      Vio_Ownership_Volatile,
      Vio_Potentially_Invalid_Dispatch,
      Vio_Potentially_Invalid_Invariant,
      Vio_Potentially_Invalid_Overlay,
      Vio_Potentially_Invalid_Part_Access,
      Vio_Potentially_Invalid_Part_Concurrent,
      Vio_Potentially_Invalid_Part_Tagged,
      Vio_Potentially_Invalid_Part_Unchecked_Union,
      Vio_Potentially_Invalid_Scalar,
      Vio_Predicate_Volatile,
      Vio_Program_Exit_Outputs,
      Vio_Real_Root,
      Vio_Relaxed_Init_Dispatch,
      Vio_Relaxed_Init_Initialized_Prefix,
      Vio_Relaxed_Init_Part_Generic, --  Any of the three following kinds
      Vio_Relaxed_Init_Part_Of_Tagged,
      Vio_Relaxed_Init_Part_Of_Unchecked_Union,
      Vio_Relaxed_Init_Part_Of_Volatile,
      Vio_Side_Effects_Call_Context,
      Vio_Side_Effects_Eq,
      Vio_Side_Effects_Traversal,
      Vio_Storage_Size,
      Vio_Subp_Variant_Structural,
      Vio_Tagged_Extension_Local,
      Vio_Target_Name_In_Call_With_Side_Effets,
      Vio_Tasking_Synchronized_Comp,
      Vio_Tasking_Unintialized_Concurrent,
      Vio_Tasking_Unsupported_Construct,
      Vio_UC_From_Access,
      Vio_UC_To_Access,
      Vio_UC_To_Access_Components,
      Vio_UC_To_Access_From,
      Vio_Unsupported_Attribute,
      Vio_Unsupported_Pragma,
      Vio_Volatile_At_Library_Level,
      Vio_Volatile_Discriminant,
      Vio_Volatile_Discriminated_Type,
      Vio_Volatile_Eq,
      Vio_Volatile_Global,
      Vio_Volatile_In_Interferring_Context,
      Vio_Volatile_Incompatible_Comp,
      Vio_Volatile_Incompatible_Type,
      Vio_Volatile_Loop_Param,
      Vio_Volatile_Parameter,
      Vio_Volatile_Result,

      --  Tool limitations

      Lim_Abstract_State_Part_Of_Concurrent_Obj,
      Lim_Access_Attr_With_Ownership_In_Unsupported_Context,
      Lim_Access_Conv,
      Lim_Access_Sub_Protected,
      Lim_Access_Sub_Traversal,
      Lim_Access_To_No_Return_Subp,
      Lim_Access_To_Relaxed_Init_Subp,
      Lim_Access_To_Subp_With_Exc,
      Lim_Access_To_Subp_With_Prog_Exit,
      Lim_Address_Attr_In_Unsupported_Context,
      Lim_Alloc_With_Type_Constraints,
      Lim_Array_Conv_Different_Size_Modular_Index,
      Lim_Array_Conv_Signed_Modular_Index,
      Lim_Assert_And_Cut_Meet_Inv,
      Lim_Borrow_Slice,
      Lim_Borrow_Traversal_First_Param,
      Lim_Borrow_Traversal_Volatile,
      Lim_Class_Attr_Of_Constrained_Type,
      Lim_Classwide_Representation_Value,
      Lim_Classwide_With_Predicate,
      Lim_Complex_Raise_Expr_In_Prec,
      Lim_Constrained_Classwide,
      Lim_Continue_Cross_Inv,
      Lim_Contract_On_Derived_Private_Type,
      Lim_Conv_Fixed_Float,
      Lim_Conv_Fixed_Integer,
      Lim_Conv_Float_Modular_128,
      Lim_Conv_Incompatible_Fixed,
      Lim_Cut_Operation_Context,
      Lim_Deep_Object_With_Addr,
      Lim_Deep_Value_In_Delta_Aggregate,
      Lim_Derived_Interface,
      Lim_Destructor,
      Lim_Entry_Family,
      Lim_Exceptional_Cases_Dispatch,
      Lim_Exceptional_Cases_Ownership,
      Lim_Exit_Cases_Dispatch,
      Lim_Ext_Aggregate_With_Type_Ancestor,
      Lim_Extension_Case_Pattern_Matching,
      Lim_GNAT_Ext_Conditional_Goto,
      Lim_GNAT_Ext_Conditional_Raise,
      Lim_GNAT_Ext_Conditional_Return,
      Lim_GNAT_Ext_Interpolated_String_Literal,
      Lim_Generic_In_Hidden_Private,
      Lim_Generic_In_Type_Inv,
      Lim_Goto_Cross_Inv,
      Lim_Hidden_Private_Relaxed_Init,
      Lim_Img_On_Non_Scalar,
      Lim_Incomplete_Type_Early_Usage,
      Lim_Indexed_Container_Aggregate,
      Lim_Inherited_Controlling_Result_From_Hidden_Part,
      Lim_Inherited_Controlling_Result_From_SPARK_Off,
      Lim_Inherited_Prim_From_Hidden_Part,
      Lim_Inherited_Prim_From_SPARK_Off,
      Lim_Iterated_Element_Association,
      Lim_Iterator_In_Component_Assoc,
      Lim_Limited_Type_From_Limited_With,
      Lim_Loop_Inv_And_Handler,
      Lim_Loop_Inv_And_Finally,
      Lim_Loop_With_Iterator_Filter,
      Lim_Max_Array_Dimension,
      Lim_Max_Modulus,
      Lim_Move_To_Access_Constant,
      Lim_No_Return_Function,
      Lim_Non_Static_Attribute,
      Lim_Multiple_Inheritance_Interfaces,
      Lim_Multiple_Inheritance_Mixed_SPARK_Mode,
      Lim_Multiple_Inheritance_Root,
      Lim_Multidim_Iterator,
      Lim_Multidim_Update,
      Lim_Null_Aggregate_In_Branching_Array_Aggregate,
      Lim_Object_Before_Inv,
      Lim_Op_Fixed_Float,
      Lim_Op_Incompatible_Fixed,
      Lim_Overlay_Uninitialized,
      Lim_Overlay_With_Deep_Object,
      Lim_Overriding_With_Precondition_Discrepancy_Hiding,
      Lim_Overriding_With_Precondition_Discrepancy_Tagged_Privacy,
      Lim_Deep_Object_Declaration_Outside_Block,
      Lim_Package_Before_Inv,
      Lim_Potentially_Invalid_Eq,
      Lim_Potentially_Invalid_Iterable,
      Lim_Potentially_Invalid_Mutable_Discr,
      Lim_Potentially_Invalid_Part_Of,
      Lim_Potentially_Invalid_Predicates,
      Lim_Potentially_Invalid_Private,
      Lim_Potentially_Invalid_Relaxed,
      Lim_Potentially_Invalid_Subp_Access,
      Lim_Potentially_Invalid_Traversal,
      Lim_Predicate_With_Different_SPARK_Mode,
      Lim_Predicate_With_Different_Visibility,
      Lim_Primitive_Call_In_DIC,
      Lim_Program_Exit_Dispatch,
      Lim_Program_Exit_Global_Modified_In_Callee,
      Lim_Protected_Operation_Of_Expression,
      Lim_Protected_Operation_Of_Component,
      Lim_Protected_Operation_Of_Formal,
      Lim_Refined_Post_On_Entry,
      Lim_Relaxed_Init_Access_Type,
      Lim_Relaxed_Init_Aliasing,
      Lim_Relaxed_Init_Invariant,
      Lim_Relaxed_Init_Variant_Part,
      Lim_Subprogram_Before_Inv,
      Lim_Subp_Variant_Duplicate,
      Lim_Subp_Variant_Eq,
      Lim_Suspension_On_Expression,
      Lim_Suspension_On_Formal,
      Lim_Target_Name_In_Borrow,
      Lim_Target_Name_In_Move,
      Lim_Type_Inv_Access_Type,
      Lim_Type_Inv_Protected_Type,
      Lim_Type_Inv_Tagged_Comp,
      Lim_Type_Inv_Tagged_Type,
      Lim_Type_Inv_Volatile,
      Lim_Uninit_Alloc_In_Expr_Fun,
      Lim_Unknown_Alignment,
      Lim_Unknown_Size,
      Lim_UU_Tagged_Comp);

   subtype Incorrect_Annotation_Kind is
     Error_Message_Kind
       range Annot_Argument_Number .. Annot_Predefined_Equality_Use_Eq;

   subtype Common_Annotation_Kind is
     Incorrect_Annotation_Kind
       range Incorrect_Annotation_Kind'First .. Annot_Wrong_Third_Parameter;

   subtype Specific_Annotation_Kind is
     Incorrect_Annotation_Kind
       range Annot_At_End_Borrow_Context .. Incorrect_Annotation_Kind'Last;

   subtype Unsupported_Kind is
     Error_Message_Kind
       range Lim_Abstract_State_Part_Of_Concurrent_Obj .. Lim_UU_Tagged_Comp;

   subtype Violation_Kind is
     Error_Message_Kind range Vio_Access_Constant .. Vio_Volatile_Result;

   subtype Marking_Error_Kind is Error_Message_Kind
   with
     Predicate =>
       Marking_Error_Kind
       in Incorrect_Annotation_Kind | Unsupported_Kind | Violation_Kind;

   subtype Default_Warning_Kind is
     Misc_Warning_Kind
       range Warn_Alias_Atomic_Vol .. Warn_Variant_Not_Recursive;
   --  These warnings are on by default

   subtype Guaranteed_Warning_Kind is
     Misc_Warning_Kind
       range Warn_Address_To_Access .. Warn_Imprecisely_Supported_Address;
   --  These warnings are guaranteed to be issued

   subtype Pedantic_Warning_Kind is
     Misc_Warning_Kind
       range Warn_Image_Attribute_Length
             .. Warn_Representation_Attribute_Value;
   --  These warnings are disabled by default and enabled collectively by
   --  "--pedantic" switch

   subtype Info_Warning_Kind is
     Misc_Warning_Kind range Warn_Comp_Relaxed_Init .. Warn_Unit_Not_SPARK;
   --  These warnings are disabled by default and enabled collectively by
   --  "--info" switch

   subtype Other_Tool_Limitation_Kind is
     Info_Warning_Kind range Warn_Comp_Relaxed_Init .. Warn_Full_View_Visible;
   --  Warnings for tool limitations

   subtype Flow_Limitation_Kind is
     Info_Warning_Kind range Warn_Alias_Array .. Warn_Tagged_Untangling;
   --  Warnings for flow limitations

   subtype Proof_Limitation_Kind is
     Info_Warning_Kind
       range Warn_Contracts_Recursive .. Warn_Set_Length_Aggregates;
   --  Warnings for proof limitations

   subtype Info_Msg_Kind is
     Misc_Warning_Kind
       range Warn_Info_Unrolling_Inlining .. Warn_Info_Unrolling_Inlining;
   --  These info messages are enabled by default.

   --  Assertion that the different warning subtypes are disjoint
   pragma
     Assert
       (for all Kind in Misc_Warning_Kind =>
          (if Kind in Default_Warning_Kind then 1 else 0)
          + (if Kind in Guaranteed_Warning_Kind then 1 else 0)
          + (if Kind in Pedantic_Warning_Kind then 1 else 0)
          + (if Kind in Info_Warning_Kind then 1 else 0)
          + (if Kind in Info_Msg_Kind then 1 else 0)
          = 1);

   --  Warning enabling/disabling mechanism

   type Warning_Enabled_Status is (WS_Enabled, WS_Disabled, WS_Error);
   --  A warning can be enabled, disabled or promoted to an error

   type Warning_Status_Array is
     array (Misc_Warning_Kind) of Warning_Enabled_Status;

   function From_Tag (Tag : String) return Misc_Warning_Kind;
   --  Compute the warning kind from a string. Raise Constraint_Error if the
   --  tag doesn't correspond to a warning kind.

   Warning_Status : Warning_Status_Array :=
     [Pedantic_Warning_Kind        => WS_Disabled,
      Info_Warning_Kind            => WS_Disabled,
      Warn_Info_Unrolling_Inlining => WS_Enabled,
      others                       => WS_Enabled];
   --  The array which contains the status for each warning. By default, all
   --  warnings are enabled, except the pedantic ones.

   function Warning_Message (Kind : Misc_Warning_Kind) return String
   is (case Kind is
         when Warn_Address_To_Access               =>
           "call to & is assumed to return a valid access"
           & " designating a valid value",
         when Warn_Alias_Atomic_Vol                =>
           "aliased objects must have the same volatility and atomic status",
         when Warn_Alias_Different_Volatility      =>
           "aliased objects have different volatile properties",
         when Warn_Attribute_Valid                 =>
           "attribute & is assumed to return True",
         when Warn_Auto_Lemma_Higher_Order         =>
           "automatically instantiated lemma is not annotated with"
           & " Higher_Order_Specialization",
         when Warn_Auto_Lemma_Calls                =>
           "automatically instantiated lemma contains calls to "
           & "& which cannot be arbitrarily specialized",
         when Warn_Auto_Lemma_Different            =>
           "automatically instantiated lemma contains several "
           & "calls to & with different specializations",
         when Warn_Auto_Lemma_Specializable        =>
           "automatically instantiated lemma does not contain any "
           & "specializable calls to &",
         when Warn_Initialization_To_Alias         =>
           "initialization of & is assumed to have no effects on"
           & " other non-volatile objects",
         when Warn_Function_Is_Valid               =>
           "function Is_Valid is assumed to return True",
         when Warn_Generic_Not_Analyzed            =>
           "generic compilation unit is not analyzed",
         when Warn_No_Possible_Termination         =>
           "procedure which does not return normally nor raises an exception"
           & " cannot always terminate",
         when Warn_Potentially_Invalid_Read        =>
           "invalid data might be read; read data is assumed to be valid in "
           & "SPARK",
         when Warn_Pragma_Annotate_No_Check        =>
           "no check message justified by this pragma",
         when Warn_Pragma_Annotate_Proved_Check    =>
           "only proved check messages justified by this pragma",
         when Warn_Pragma_Annotate_Terminating     =>
           "Terminating, Always_Return, and Might_Not_Return annotations are"
           & " deprecated, ignored",
         when Warn_Pragma_External_Axiomatization  =>
           "External Axiomatizations are not supported anymore, ignored",
         when Warn_Pragma_Ignored                  =>
           "pragma & ignored (not yet supported)",
         when Warn_Pragma_Overflow_Mode            =>
           "pragma Overflow_Mode in code is ignored",
         when Warn_Precondition_Statically_False   =>
           "precondition is statically False",
         when Warn_Restriction_Ignored             =>
           "restriction & ignored (not yet supported)",
         when Warn_Unreferenced_Function           =>
           "analyzing unreferenced function &",
         when Warn_Unreferenced_Procedure          =>
           "analyzing unreferenced procedure &",
         when Warn_Useless_Potentially_Invalid_Obj =>
           "& cannot have invalid values",
         when Warn_Useless_Potentially_Invalid_Fun =>
           "the result of & cannot have invalid values",
         when Warn_Useless_Relaxed_Init_Fun        =>
           "the result of & cannot be partially initialized",
         when Warn_Useless_Relaxed_Init_Obj        =>
           "& cannot be partially initialized",
         when Warn_Variant_Not_Recursive           =>
           "no recursive call visible",

         --  Warnings guaranteed to be issued
         when Warn_Assumed_Always_Terminates       =>
           "no Always_Terminates aspect available for &",
         when Warn_Assumed_Global_Null             =>
           "no Global contract available for &",
         --  The warning message is customized depending on the assumptions
         --  that need to be checked.
         when Warn_Imprecisely_Supported_Address   =>
           "address specification on & is imprecisely supported",

         --  Warnings enabled with --pedantic switch
         when Warn_Image_Attribute_Length          =>
           "attribute & has an implementation-defined length",
         when Warn_Operator_Reassociation          =>
           "possible reassociation due to missing parentheses",
         when Warn_Representation_Attribute_Value  =>
           "attribute & has an implementation-defined value",

         --  Warnings enabled with --info switch
         when Warn_Unit_Not_SPARK                  =>
           "SPARK_Mode not applied to this compilation unit",

         --  Tool limitations
         when Warn_Comp_Relaxed_Init               =>
           "& is handled as if it was annotated with Relaxed_Initialization "
           & "as all its components are annotated that way",
         when Warn_Full_View_Visible               =>
           "full view of & declared # is visible when analyzing &",

         --  Flow limitations
         when Warn_Alias_Array                     =>
           "aliasing check on components of an array is handled imprecisely",
         when Warn_Imprecise_GG                    =>
           "global generation of & might be imprecise",
         when Warn_Init_Array                      =>
           "initialization of an array in FOR loop is handled imprecisely",
         when Warn_Init_Multidim_Array             =>
           "initialization of a multi-dimensional array in nested FOR loops "
           & "is handled imprecisely",
         when Warn_Tagged_Untangling               =>
           "flow of dependencies on & is handled imprecisely",

         --  Proof limitations
         when Warn_Contracts_Recursive             =>
           "& is recursive; (implicit) contract of mutally recursive "
           & "functions might not be available on calls from contracts and "
           & "assertions",
         when Warn_Proof_Module_Cyclic             =>
           "references between entities introduce a cycle in proof "
           & "dependencies; (implicit) contract of mutally dependent "
           & "functions might not be available on calls from contracts and "
           & "assertions",
         when Warn_DIC_Ignored                     =>
           "default initial condition on type & not available for proof in an "
           & "assertion context",
         when Warn_Imprecise_Address               =>
           "adress of object is not precisely known",
         when Warn_Imprecise_Align                 =>
           "alignment of object is not precisely known",
         when Warn_Imprecise_Call                  =>
           "call to & is not handled precisely",
         when Warn_Imprecise_String_Literal        =>
           "value of string literal is not handled precisely",
         when Warn_Component_Size                  =>
           "the value of attribute Component_Size is handled in an imprecise "
           & "way",
         when Warn_Record_Component_Attr           =>
           "the value of attribute & is handled in an imprecise way",
         when Warn_Imprecise_Size                  =>
           "the value of attribute & is handled in an imprecise way",
         when Warn_Imprecise_Overlay               =>
           "imprecise handling of overlay (&)",
         when Warn_Imprecise_UC                    =>
           "imprecise handling of Unchecked_Conversion (&)",
         when Warn_Imprecise_Value                 =>
           "references to the ""Value"" attribute are handled in an imprecise "
           & "way, so the precondition is impossible to prove and nothing "
           & "will be known about the evaluation of the attribute reference",
         when Warn_Imprecise_Image                 =>
           "references to the & attribute are handled in an"
           & " imprecise way, so nothing will be known about the evaluation"
           & " of the attribute reference apart from a bound on its length",
         when Warn_Loop_Entity                     =>
           "The initial value of & declared before the loop invariant "
           & "is not visible after the invariant; it shall be restated in the "
           & "invariant if necessary",
         when Warn_Init_Cond_Ignored               =>
           "Initial_Condition of package & is ignored",
         when Warn_No_Reclam_Func                  =>
           "no reclamation function nor reclaimed value found for type with "
           & "ownership &",
         when Warn_Map_Length_Aggregates           =>
           "no ""Length"" function found for type with predefined map "
           & "aggregates &",
         when Warn_Set_Length_Aggregates           =>
           "no ""Length"" function found for type with predefined set "
           & "aggregates &",
         when Warn_Relaxed_Init_Mutable_Discr      =>
           "mutable discriminants of a standalone object or parameter with "
           & "relaxed initialization are enforced to always be initialized",
         when Warn_Predef_Eq_Null                  =>
           "no null value found for type with predefined equality &",

         --  info messages enabled by default
         when Warn_Info_Unrolling_Inlining         =>
           --  these messages are issued by the front-end
           raise Program_Error);

   function Error_Message (Kind : Error_Message_Kind) return String
   with Pre => Kind not in Marking_Error_Kind;
   --  Return the error message for each kind of error except violations and
   --  limitations which are handled specificaly.

   function Unsupported_Message
     (Kind       : Unsupported_Kind;
      Name       : String := "";
      Root_Cause : Boolean := False) return String
   is (case Kind is
         when Lim_Abstract_State_Part_Of_Concurrent_Obj                   =>
           "abstract state Part_Of constituent of a single concurrent object",
         when Lim_Access_Attr_With_Ownership_In_Unsupported_Context       =>
           """Access"" attribute of a type with ownership not directly inside"
           & " an assignment statement, an object declaration, or a simple"
           & " return statement",
         when Lim_Access_Conv                                             =>
           "conversion between access types with"
           & " different designated types",
         when Lim_Access_Sub_Protected                                    =>
           "access to protected subprogram",
         when Lim_Access_Sub_Traversal                                    =>
           "access to borrowing traversal function",
         when Lim_Access_To_No_Return_Subp                                =>
           "access to No_Return procedure",
         when Lim_Access_To_Relaxed_Init_Subp                             =>
           "access to subprogram annotated with Relaxed_Initialization",
         when Lim_Access_To_Subp_With_Exc                                 =>
           "access to procedure which might propagate exceptions",
         when Lim_Access_To_Subp_With_Prog_Exit                           =>
           "access to procedure which might exit the program",
         when Lim_Address_Attr_In_Unsupported_Context                     =>
           "attribute ""Address"" in unsupported context",
         when Lim_Alloc_With_Type_Constraints                             =>
           "uninitialized allocator with type constraints",
         when Lim_Continue_Cross_Inv                                      =>
           "continue statement preceding loop-invariant",
         when Lim_Object_Before_Inv                                       =>
           "non-scalar object or object with address clause declared before"
           & " loop-invariant",
         when Lim_Package_Before_Inv                                      =>
           "nested packages before loop-invariant",
         when Lim_Subprogram_Before_Inv                                   =>
           "nested subprogram before loop-invariant",
         when Lim_Subp_Variant_Eq                                         =>
           "subprogram variant on a user-defined equality on record type",
         when Lim_Subp_Variant_Duplicate                                  =>
           "multiple subprogram variants on a subprogram",
         when Lim_Goto_Cross_Inv                                          =>
           "goto statement to label located inside the loop crossing the loop"
           & " invariant",
         when Lim_Assert_And_Cut_Meet_Inv                                 =>
           "pragma Assert_And_Cut immediately within a sequence of statements"
           & " containing a loop invariant",
         when Lim_Multidim_Update                                         =>
           "attribute ""Update"" of unconstrained multidimensional array",
         when Lim_Null_Aggregate_In_Branching_Array_Aggregate             =>
           "null aggregate as subaggregate of a multidimensional array"
           & " aggregate with multiple associations",
         when Lim_Uninit_Alloc_In_Expr_Fun                                =>
           "uninitialized allocator inside expression function",
         when Lim_Iterator_In_Component_Assoc                             =>
           "iterated component association with iterator specification",
         when Lim_Exceptional_Cases_Dispatch                              =>
           "aspect ""Exceptional_Cases"" on dispatching operation",
         when Lim_Exceptional_Cases_Ownership                             =>
           (if Root_Cause
            then "exception propagation and parameters with ownership"
            else
              "procedure which might propagate exceptions with parameters "
              & "of mode ""in out"" or ""out"" subjected to ownership which "
              & "might not be passed by reference"),
         when Lim_Exit_Cases_Dispatch                                     =>
           "aspect ""Exit_Cases"" on dispatching operation",
         when Lim_Program_Exit_Dispatch                                   =>
           "aspect ""Program_Exit"" on dispatching operation",
         when Lim_Program_Exit_Global_Modified_In_Callee                  =>
           (if Root_Cause or Name = ""
            then
              "call which might exit the program and leave outputs"
              & " in an inconsistent state"
            else
              "call which might exit the program and leave "
              & Name
              & " mentioned in the postcondition of & in an inconsistent "
              & "state"),
         when Lim_Ext_Aggregate_With_Type_Ancestor                        =>
           "extension aggregate with subtype ancestor part",
         when Lim_Extension_Case_Pattern_Matching                         =>
           "GNAT extension for case pattern matching",
         when Lim_GNAT_Ext_Conditional_Goto                               =>
           "GNAT extension for conditional goto",
         when Lim_GNAT_Ext_Conditional_Raise                              =>
           "GNAT extension for conditional raise",
         when Lim_GNAT_Ext_Conditional_Return                             =>
           "GNAT extension for conditional return",
         when Lim_GNAT_Ext_Interpolated_String_Literal                    =>
           "GNAT extension for interpolated string literal",
         when Lim_Iterated_Element_Association                            =>
           "iterated element association",
         when Lim_Multidim_Iterator                                       =>
           "iterator specification over multi-dimensional array",
         when Lim_Loop_Inv_And_Handler                                    =>
           "loop invariant in a list of statements with an exception handler",
         when Lim_Loop_Inv_And_Finally                                    =>
           "loop invariant in a list of statements with a finally section",
         when Lim_Loop_With_Iterator_Filter                               =>
           "loop on an iterator specification with an iterator filter",
         when Lim_Complex_Raise_Expr_In_Prec                              =>
           "raise expression in a complex expression in a precondition",
         when Lim_Array_Conv_Different_Size_Modular_Index                 =>
           "conversion between array types with modular index types of"
           & " different sizes",
         when Lim_Array_Conv_Signed_Modular_Index                         =>
           "conversion between array types with modular and non-modular index"
           & " types",
         when Lim_Move_To_Access_Constant                                 =>
           "move as part of an allocator or a conversion to an "
           & "access-to-constant type which does not occur directly inside"
           & " an assignment statement, an object declaration, or a simple"
           & " return statement",
         when Lim_Conv_Fixed_Float                                        =>
           "conversion between fixed-point and floating-point types",
         when Lim_Conv_Incompatible_Fixed                                 =>
           "conversion between incompatible fixed-point types",
         when Lim_Conv_Fixed_Integer                                      =>
           "conversion between fixed-point and integer types",
         when Lim_Conv_Float_Modular_128                                  =>
           "conversion between floating-point and 128-bits modular types",
         when Lim_Cut_Operation_Context                                   =>
           "call to a cut operation in an unsupported context",
         when Lim_Target_Name_In_Borrow                                   =>
           "@ inside a reborrow",
         when Lim_Target_Name_In_Move                                     =>
           "@ inside a move assignment",
         when Lim_Deep_Object_With_Addr                                   =>
           "address clause on an object of an ownership type",
         when Lim_Deep_Value_In_Delta_Aggregate                           =>
           "delta aggregate with possible aliasing of components of an "
           & "ownership type",
         when Lim_Derived_Interface                                       =>
           "interface derived from other interfaces",
         when Lim_Destructor                                              =>
           "record type with a destructor",
         when Lim_Overlay_Uninitialized                                   =>
           "object with an address clause which is not fully initialized at "
           & "declaration",
         when Lim_Overlay_With_Deep_Object                                =>
           "overlay with an object of an ownership type",
         when Lim_Deep_Object_Declaration_Outside_Block                   =>
           "declaration of an object of an ownership type outside a block "
           & "for declarations",
         when Lim_Non_Static_Attribute                                    =>
           "non-static attribute"
           & (if Name = ""
              then ""
              else " """ & Standard_Ada_Case (Name) & """"),
         when Lim_Img_On_Non_Scalar                                       =>
           (if Name = ""
            then "attribute ""Image"" on non-scalar type"
            else
              "attribute """
              & Standard_Ada_Case (Name)
              & """ on non-scalar type"),
         when Lim_Incomplete_Type_Early_Usage                             =>
           "usage of incomplete type completed in package body outside of an "
           & "access type declaration",
         when Lim_Inherited_Controlling_Result_From_Hidden_Part           =>
           "tagged type with inherited primitive subprograms with controlling"
           & " result and hidden private extension",
         when Lim_Inherited_Controlling_Result_From_SPARK_Off             =>
           "tagged type with inherited primitive subprograms with controlling"
           & " result and private extension outside SPARK",
         when Lim_Inherited_Prim_From_Hidden_Part                         =>
           "tagged type with primitive subprograms inherited from a type"
           & " declared in a hidden private part",
         when Lim_Inherited_Prim_From_SPARK_Off                           =>
           "tagged type with primitive subprograms inherited from a type"
           & " declared in a private part with SPARK_Mode Off",
         when Lim_Unknown_Alignment                                       =>
           "unknown value of object alignment",
         when Lim_Unknown_Size                                            =>
           "unknown value of object size",
         when Lim_Op_Fixed_Float                                          =>
           "operation between fixed-point and floating-point types",
         when Lim_Op_Incompatible_Fixed                                   =>
           "operation between incompatible fixed-point types",
         when Lim_Protected_Operation_Of_Expression                       =>
           "call to operation of a dereference",
         when Lim_Protected_Operation_Of_Formal                           =>
           "call to operation of a formal protected parameter",
         when Lim_Protected_Operation_Of_Component                        =>
           "call to operation of a component of a protected type",
         when Lim_Suspension_On_Expression                                =>
           "suspension on a dereference",
         when Lim_Suspension_On_Formal                                    =>
           "suspension on a formal parameter",
         when Lim_Borrow_Slice                                            =>
           "borrow through a slice",
         when Lim_Borrow_Traversal_First_Param                            =>
           "borrowing traversal functions whose first parameter does not have"
           & " an anonymous access-to-variable type",
         when Lim_Borrow_Traversal_Volatile                               =>
           "volatile borrowing traversal function",
         when Lim_No_Return_Function                                      =>
           "function annotated with No_Return",
         when Lim_Multiple_Inheritance_Root                               =>
           "subprogram inherited from root and interface",
         when Lim_Multiple_Inheritance_Interfaces                         =>
           "subprogram inherited from multiple interfaces",
         when Lim_Multiple_Inheritance_Mixed_SPARK_Mode                   =>
           "subprogram implicitly inherited from multiple progenitor types"
           & " with conflicting SPARK mode",
         when Lim_Overriding_With_Precondition_Discrepancy_Hiding         =>
           "dispatching primitive subprogram overriding with class-wide"
           & " precondition inherited from a potentially hidden ancestor",
         when Lim_Overriding_With_Precondition_Discrepancy_Tagged_Privacy =>
           "dispatching primitive subprogram overriding declared for a"
           & " private untagged type with no precondition and a class-wide"
           & " precondition inherited from ancestor",
         when Lim_Potentially_Invalid_Eq                                  =>
           "Potentially_Invalid aspect on the primitive equality of a record "
           & "type",
         when Lim_Potentially_Invalid_Iterable                            =>
           "Potentially_Invalid aspect on a function associated to the aspect"
           & " Iterable",
         when Lim_Potentially_Invalid_Mutable_Discr                       =>
           "part of potentially invalid object with mutable discriminants",
         when Lim_Potentially_Invalid_Part_Of                             =>
           "potentially invalid object marked Part_Of a protected object",
         when Lim_Potentially_Invalid_Predicates                          =>
           "potentially invalid object with a part subject to predicates",
         when Lim_Potentially_Invalid_Private                             =>
           "potentially invalid object with a part whose full view is not in "
           & "SPARK",
         when Lim_Potentially_Invalid_Relaxed                             =>
           "potentially invalid object with a part with relaxed "
           & "initialization",
         when Lim_Potentially_Invalid_Subp_Access                         =>
           "access to a subprogram annotated with Potentially_Invalid",
         when Lim_Potentially_Invalid_Traversal                           =>
           "traversal function with a potentially invalid traversed "
           & "parameter",
         when Lim_Primitive_Call_In_DIC                                   =>
           "primitive calls in default initial condition",
         when Lim_Constrained_Classwide                                   =>
           "constrained class-wide subtype",
         when Lim_Type_Inv_Access_Type                                    =>
           "access to incomplete or private type which needs an invariant"
           & " check",
         when Lim_Type_Inv_Protected_Type                                 =>
           "type invariant on protected types",
         when Lim_Type_Inv_Tagged_Type                                    =>
           "type invariant on tagged types",
         when Lim_Type_Inv_Volatile                                       =>
           "volatile object with asynchronous writers or readers and a type"
           & " invariant",
         when Lim_Type_Inv_Tagged_Comp                                    =>
           "type invariant on components of tagged types",
         when Lim_Max_Array_Dimension                                     =>
           "array of dimension greater than" & Max_Array_Dimensions'Img,
         when Lim_Max_Modulus                                             =>
           "modulus greater than 2 '*'* 128",
         when Lim_Class_Attr_Of_Constrained_Type                          =>
           "attribute ""Class"" of a constrained type",
         when Lim_Classwide_Representation_Value                          =>
           "representation attribute on class-wide value",
         when Lim_Classwide_With_Predicate                                =>
           "subtype predicate on a classwide type",
         when Lim_Contract_On_Derived_Private_Type                        =>
           "type aspect on type derived from a private type",
         when Lim_Predicate_With_Different_SPARK_Mode                     =>
           "type with predicates with different SPARK_Mode values",
         when Lim_Predicate_With_Different_Visibility                     =>
           "type with predicates with different visibility",
         when Lim_UU_Tagged_Comp                                          =>
           "component of an unconstrained unchecked union type in a tagged"
           & " extension",
         when Lim_Relaxed_Init_Invariant                                  =>
           "invariant on a type used as a subcomponent of a type or"
           & " an object annotated with relaxed initialization",
         when Lim_Relaxed_Init_Access_Type                                =>
           "access-to-subprogram type used as a subcomponent of a type or"
           & " an object annotated with relaxed initialization",
         when Lim_Relaxed_Init_Aliasing                                   =>
           "relaxed initialization on overlaid objects",
         when Lim_Relaxed_Init_Variant_Part                               =>
           "subtype with a discriminant constraint containing only"
           & " subcomponents whose type is annotated with"
           & " Relaxed_Initialization",
         when Lim_Limited_Type_From_Limited_With                          =>
           (if Root_Cause
            then "limited view coming from limited with"
            else "limited view of type & coming from limited with"),
         when Lim_Refined_Post_On_Entry                                   =>
           "Refined_Post aspect on a protected entry",
         when Lim_Entry_Family                                            =>
           "entry family",
         when Lim_Generic_In_Hidden_Private                               =>
           "instance of a generic unit declared in a package whose private "
           & "part is hidden outside of this package",
         when Lim_Generic_In_Type_Inv                                     =>
           "instance of a generic unit declared in a package containing a "
           & "type with an invariant outside of this package",
         when Lim_Hidden_Private_Relaxed_Init                             =>
           "hidden private type containing only subcomponents whose type is"
           & " annotated with Relaxed_Initialization",
         when Lim_Indexed_Container_Aggregate                             =>
           "indexed container aggregate");

   type Annot_Format_Kind is (Text_Form, Aspect_Form, Pragma_Form);

   function Aspect_Or_Pragma (From_Aspect : Boolean) return Annot_Format_Kind
   is (if From_Aspect then Aspect_Form else Pragma_Form);

   function Annot_To_String
     (Kind     : Incorrect_Annotation_Kind := Common_Annotation_Kind'First;
      Format   : Annot_Format_Kind := Text_Form;
      Name     : String := "";
      Snd_Name : String := "") return String;
   --  Pretty print annotation for error.
   --  Get the name of the annotation from the Kind if it is specific,
   --  otherwise, it can be supplied in Name or left empty (the annotation
   --  will then use GNATprove only.
   --  If Format is
   --   * Text_Form, output: "Name" annotation
   --   * Pragma_Form, output: "pragma Annotate (GNATprove, Name, [...])"
   --   * Aspect_Form, output: aspect "Annotate => (GNATprove, Name, [...])"
   --  If Snd_Name is supplied, it will be used as a string for the third
   --  parameter of the aspect.

   function Incorrect_Annotation_Message
     (Kind        : Incorrect_Annotation_Kind;
      From_Aspect : Boolean;
      Name        : String;
      Snd_Name    : String) return String;
   --  Create a message for an incorrect annotation for an aspect or pragma
   --  Annotate.

   function Violation_Message
     (Kind       : Violation_Kind;
      Name       : String := "";
      Root_Cause : Boolean := False) return String;
   --  If Root_Cause is True, return the message that should be used as root
   --  cause message for cascading violations for Kind if it is different from
   --  the regular message (typically, if it has character insertions).

   --  Explain codes are used in GNATprove to provide more information on
   --  selected error/warning messages. The subset of those codes used in
   --  the frontend are redefined in Errout.

   type Explain_Code_Kind is
     (EC_None,
      EC_Volatile_At_Library_Level,
      EC_Address_In_Expression,
      EC_Type_Early_Call_Region,
      EC_Volatile_Non_Interfering_Context,
      EC_Function_Output_Global,
      EC_Function_Volatile_Input_Global,
      EC_Variable_Input_In_Expression,
      EC_Write_In_Elaboration,
      EC_Required_Part_Of,
      EC_Ownership_Moved_Object,
      EC_SPARK_Mode_On_Not_Library_Level,
      EC_Address_Spec_Imprecise_Warn,
      EC_Always_Terminates_Warn,
      EC_Output_In_Function_Global_Or_Depends,
      EC_Out_Parameter_In_Function,
      EC_Always_Terminates_On_Function,
      EC_Exceptional_Cases_On_Function,
      EC_Call_To_Function_With_Side_Effects,
      EC_Uninitialized_Allocator,
      EC_Incorrect_Source_Of_Borrow);
   for Explain_Code_Kind use
     (EC_None                                 => 0,
      EC_Volatile_At_Library_Level            => 1,
      EC_Address_In_Expression                => 2,
      EC_Type_Early_Call_Region               => 3,
      EC_Volatile_Non_Interfering_Context     => 4,
      EC_Function_Output_Global               => 5,
      EC_Function_Volatile_Input_Global       => 6,
      EC_Variable_Input_In_Expression         => 7,
      EC_Write_In_Elaboration                 => 8,
      EC_Required_Part_Of                     => 9,
      EC_Ownership_Moved_Object               => 10,
      EC_SPARK_Mode_On_Not_Library_Level      => 11,
      EC_Address_Spec_Imprecise_Warn          => 12,
      EC_Always_Terminates_Warn               => 13,
      EC_Output_In_Function_Global_Or_Depends => 14,
      EC_Out_Parameter_In_Function            => 15,
      EC_Always_Terminates_On_Function        => 16,
      EC_Exceptional_Cases_On_Function        => 17,
      EC_Call_To_Function_With_Side_Effects   => 18,
      EC_Uninitialized_Allocator              => 19,
      EC_Incorrect_Source_Of_Borrow           => 20);

   function To_String (Code : Explain_Code_Kind) return String
   with Pre => Code /= EC_None;
   --  Return the error code to include in the message, in the same format used
   --  by Errout procedures.

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

   function SRM_Reference (Kind : Violation_Kind) return String
   with
     Post =>
       SRM_Reference'Result = ""
       or else
         (SRM_Reference'Result'Length > 9
          and then Head (SRM_Reference'Result, 9) = "SPARK RM ");
   --  Return a reference to the SRM for Kind if any

   function Explain_Code (Kind : Violation_Kind) return Explain_Code_Kind;
   --  Return an explain code to be displayed along with the error message for
   --  Kind if any. If SRM_Reference
   --  is set, the reference to the SRM is appended to the error message. If
   --  Cont_Msg is set, a continuation message is issued. If Root_Cause_Msg
   --  is set, the corresponding message is used as root cause message for
   --  cascading violations (typically used if Msg has character insertions).

   function Annotation_From_Kind
     (Kind : Specific_Annotation_Kind) return String;
   --  Return the name of the annotation from its kind. It is used to compute
   --  the root cause for incorrect uses of annotations.

   function Locate_On_First_Token (V : VC_Kind) return Boolean
   is (case V is
         when VC_RTE_Kind     => False,
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

   Data_Representation_Subdir_Name : constant String := "data_representation";
   --  Subdir of "gnatprove" where the data representation files are generated

   SPARK_Suffix : constant String := "spark";
   --  Extension of the files where spark_report expects gnat2why results

   type SPARK_Mode_Status is
     (All_In_SPARK,       --  Spec (and if applicable, body) are in SPARK
      Spec_Only_In_SPARK, --  Only spec is in SPARK, body is not in SPARK
      Not_In_SPARK);      --  Not in SPARK

   type GP_Mode is (GPM_Check, GPM_Check_All, GPM_Flow, GPM_Prove, GPM_All);
   --  The feature modes of GNATprove are:
   --  * GPM_Check     : Check SPARK rules
   --  * GPM_Check_All : Check all SPARK rules, including the ones checked
   --                    during flow analysis.
   --  * GPM_Prove     : Check validity of contracts, proof of subprogram
   --                    bodies.
   --  * GPM_Flow      : Check validity of Globals, Depends
   --  * GPM_All       : Union of GPM_Prove and GPM_Flow

   ------------
   -- Labels --
   ------------

   --  These strings are used in Why3 labels to communicate information to
   --  Why3. Changes here should be propagated to the code of gnatwhy3. In
   --  gnat2why, use of the corresponding Name_Ids in Why.Atree.Modules is
   --  preferred over using the strings here.

   GP_Check_Marker      : constant String := "GP_Check:";
   GP_Pretty_Ada_Marker : constant String := "GP_Pretty_Ada:";
   GP_Shape_Marker      : constant String := "GP_Shape:";
   GP_Inline_Marker     : constant String := "GP_Inline";
   GP_Inlined_Marker    : constant String := "GP_Inlined";

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

   --------------------
   --  Data Exchange --
   --------------------

   --  Constants that are used in the extra_info returned from gnatwhy3, to
   --  identify lower and upper bound of a range check.

   Low_Bound_Id  : constant Integer := -1;
   High_Bound_Id : constant Integer := -2;

   --  Type for the extra_info returned from gnatwhy3
   type Prover_Extra_Info is record
      Info   : Integer := 0;
      --  Either a node ID or one of the bound id constants
      Inline : Integer := 0;
      --  Either 0 if no inlining, a node ID, or a negative value if there is
      --  no such node.
   end record;

   --  This section defines various types that are used to communicate between
   --  the various gnatprove processes (most notably between gnat2why/gnatwhy3
   --  and gnat2why/spark_report). Also, JSON conversion functions are defined.

   type Prover_Stat is record
      Count     : Natural;
      Max_Steps : Natural;
      Max_Time  : Float;
   end record;

   package Prover_Stat_Maps is new
     Ada.Containers.Indefinite_Ordered_Maps
       (Key_Type     => String,
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

   type CEE_Kind is
     (CEE_Variable, CEE_Error_Msg, CEE_Old, CEE_Result, CEE_Other);

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
            | Float_NaN
         =>
            null;

         when Float_Val =>
            F_Sign        : Unbounded_String;
            F_Exponent    : Unbounded_String;
            F_Significand : Unbounded_String;
      end case;
   end record;

   type Float_Value_Ptr is not null access constant Float_Value;

   type Cntexmp_Value;
   type Cntexmp_Value_Ptr is access constant Cntexmp_Value;

   package Cntexmp_Value_Array is new
     Ada.Containers.Indefinite_Ordered_Maps
       (Key_Type     => String, -- Indices can exceed MAX_INT
        Element_Type => Cntexmp_Value_Ptr);
   --  Map of counterexample values.
   --  In the case of counterexample array, the Key_Type represents the index.

   type Cntexmp_Value (T : Cntexmp_Type := Cnt_Invalid) is record
      case T is
         when Cnt_Integer =>
            I : Unbounded_String;

         when Cnt_Decimal =>
            D : Unbounded_String;

         when Cnt_Float =>
            F : Float_Value_Ptr;

         when Cnt_Boolean =>
            Bo : Boolean;

         when Cnt_Bitvector =>
            B : Unbounded_String;

         when Cnt_Record =>
            Fi : Cntexmp_Value_Array.Map;

         when Cnt_Projection =>
            Er : Unbounded_String;
            --  Cnt_projection is an error case anywhere after vc_kinds

         when Cnt_Array =>
            Array_Indices : Cntexmp_Value_Array.Map;
            Array_Others  : Cntexmp_Value_Ptr;

         when Cnt_Invalid =>
            S : Unbounded_String;
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
   --  component Elems gives the value of individual non-others non-null
   --  subcomponents, to be used if the Count is too large for printing Str.

   type Cntexample_Kind is (Raw, Pretty_Printed, Json_Format);

   type Cntexample_Elt (K : Cntexample_Kind := Raw) is record
      Kind : CEE_Kind;
      Name : Unbounded_String;
      case K is
         when Raw =>
            Labels : S_String_List.List;
            Value  : Cntexmp_Value_Ptr;

         when Pretty_Printed =>
            Val_Str : CNT_Unbounded_String;

         when Json_Format =>
            JSON_Obj : JSON_Value := Create_Object;
      end case;
   end record;

   package Cntexample_Elt_Maps is new
     Ada.Containers.Indefinite_Ordered_Maps
       (Key_Type     => String,
        Element_Type => Cntexample_Elt,
        "<"          => "<",
        "="          => "=");

   function Eq_List (A, B : Cntexample_Elt) return Boolean
   is (A.Name = B.Name);

   package Cntexample_Elt_Lists is new
     Ada.Containers.Doubly_Linked_Lists
       (Element_Type => Cntexample_Elt,
        "="          => Eq_List);

   package Cntexample_Line_Maps is new
     Ada.Containers.Ordered_Maps
       (Key_Type     => Natural,
        Element_Type => Cntexample_Elt_Lists.List,
        "<"          => "<",
        "="          => Cntexample_Elt_Lists."=");

   type Previous_Line is record
      Line_Cnt : Cntexample_Elt_Lists.List;
      Ada_Node : Integer;  --  Node_Id of the Loop_Invariant
   end record;

   function Eq_previous (A, B : Previous_Line) return Boolean
   is (Cntexample_Elt_Lists."=" (A.Line_Cnt, B.Line_Cnt));

   package Previous_Line_Maps is new
     Ada.Containers.Ordered_Maps
       (Key_Type     => Natural,
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
     Ada.Containers.Indefinite_Ordered_Maps
       (Key_Type     => String,
        Element_Type => Cntexample_Lines,
        "<"          => "<",
        "="          => "=");

   --  Type used to store the inputs and location of the subprogram that
   --  lead to the generation of the counterexample
   type Json_Formatted_Input is record
      Input_As_JSON : Cntexample_Elt_Lists.List := Cntexample_Elt_Lists.Empty;
      File          : Unbounded_String := To_Unbounded_String ("");
      Line          : Natural := 0;
   end record;

   type Cntexample_Data is record
      Map           : Cntexample_File_Maps.Map := Cntexample_File_Maps.Empty;
      Input_As_JSON : Json_Formatted_Input;
   end record;

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

   subtype Cntexmp_Confirmed_Verdict_Category is
     Cntexmp_Verdict_Category
       range Non_Conformity .. Non_Conformity_Or_Subcontract_Weakness;
   --  The categories of confirmed counterexamples

   type Cntexmp_Verdict
     (Verdict_Category : Cntexmp_Verdict_Category := Not_Checked)
   is record
      case Verdict_Category is
         when Bad_Counterexample | Incomplete | Not_Checked =>
            Verdict_Reason : Unbounded_String :=
              To_Unbounded_String ("Unknown");

         when Cntexmp_Confirmed_Verdict_Category =>
            CE         : Cntexample_Data;
            Extra_Info : Prover_Extra_Info;
      end case;
   end record;
   --  The result when checking the counterexample for a check, based on Why3
   --  giant-step RAC and SPARK small-step RAC. Store a counterexample value
   --  and extra information for the check location.

   function Reason (Verdict : Cntexmp_Verdict) return String
   is (case Verdict.Verdict_Category is
         when Bad_Counterexample | Not_Checked | Incomplete =>
           To_String (Verdict.Verdict_Reason),
         when others                                        => "");
   --  Return the reason for a verdict (empty for confirmed verdicts)

   function To_String (P : Prover_Category) return String;
   --  Return a user-visible string to describe the category of prover

   function From_JSON (V : JSON_Value) return Prover_Stat;
   function From_JSON (V : JSON_Value) return Prover_Stat_Maps.Map;
   function From_JSON (V : JSON_Value) return Prover_Category;
   function From_JSON (V : JSON_Value) return Cntexample_File_Maps.Map;
   function From_JSON (V : JSON_Value) return SPARK_Mode_Status;
   function From_JSON (V : JSON_Value) return GP_Mode;
   function From_JSON (V : JSON_Value) return Warning_Status_Array;

   function From_JSON_Labels (Ar : JSON_Array) return S_String_List.List;

   function To_JSON (M : Prover_Stat_Maps.Map) return JSON_Value;
   function To_JSON (P : Prover_Category) return JSON_Value;
   function To_JSON (F : Cntexample_File_Maps.Map) return JSON_Value;
   function To_JSON (V : Cntexmp_Value) return JSON_Value;
   function To_JSON (Status : SPARK_Mode_Status) return JSON_Value;
   function To_JSON (M : GP_Mode) return JSON_Value;
   function To_JSON (W : Warning_Status_Array) return JSON_Value;
   function To_JSON (L : Cntexample_Elt_Lists.List) return JSON_Value;
   function To_JSON (S : Json_Formatted_Input) return JSON_Value;
end VC_Kinds;
