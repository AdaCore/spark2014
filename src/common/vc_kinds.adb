------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                              V C _ K I N D S                             --
--                                                                          --
--                                 B o d y                                  --
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

package body VC_Kinds is

   function To_JSON (S : Prover_Stat) return JSON_Value;
   function To_JSON (L : Cntexample_Lines) return JSON_Value;
   function To_JSON (C : Cntexample_Elt) return JSON_Value;
   function To_JSON (K : CEE_Kind) return JSON_Value;

   function From_JSON (V : JSON_Value) return Cntexample_Lines;
   function From_JSON (V : JSON_Value) return Cntexample_Elt;
   function From_JSON (V : JSON_Value) return Cntexample_Elt_Lists.List;
   function From_JSON (V : JSON_Value) return CEE_Kind;
   function From_JSON (V : JSON_Value) return Cntexmp_Type;

   function Get_Typed_Cntexmp_Value (V : JSON_Value) return Cntexmp_Value;

   function Wrap_CWE (S : String) return String;
   --  If non-empty, wrap the string S so that it becomes "[CWE <S>]"

   ------------
   -- CWE_ID --
   ------------

   function CWE_ID (Kind : VC_Kind) return String is
   begin
      return
        (case Kind is
           --  CWE-369: Divide By Zero

           when VC_Division_Check                                   => "369",

           --  CWE-119: Improper Restriction of Operations within the Bounds of
           --  a Memory Buffer.

           when VC_Index_Check                                      => "119",

           --  CWE-190: Integer Overflow or Wraparound

           when VC_Overflow_Check                                   => "190",

           --  CWE-739: CWE CATEGORY: CERT C Secure Coding Section 05 -
           --  Floating Point (FLP)

           when VC_FP_Overflow_Check                                => "739",

           --  CWE-682: Incorrect Calculation

           when VC_Range_Check
              | VC_Predicate_Check
              | VC_Predicate_Check_On_Default_Value                 => "682",

           --  CWE-136: CWE CATEGORY: Type Errors

           when VC_Discriminant_Check | VC_Tag_Check                => "136",

           --  CWE-835: Loop with Unreachable Exit Condition ('Infinite Loop')

           when VC_Loop_Variant                                     => "835",

           --  CWE-772: Missing Release of Resource after Effective Lifetime

           when VC_Resource_Leak | VC_Resource_Leak_At_End_Of_Scope => "772",

           --  CWE-476: NULL Pointer Dereference

           when VC_Null_Pointer_Dereference                         => "476",

           --  CWE-457: Use of Uninitialized Variable

           when VC_Initialization_Check                             => "457",

           --  CWE-628: Function Call with Incorrectly Specified Arguments

           when VC_Precondition | VC_Precondition_Main              => "628",

           --  CWE-682: Incorrect Calculation

           when VC_Postcondition
              | VC_Refined_Post
              | VC_Exceptional_Case
              | VC_Exit_Case
              | VC_Program_Exit_Post
              | VC_Contract_Case                                    => "682",

           --  CWE-843 Access of Resource Using Incompatible Type ('Type
           --  Confusion')

           when VC_UC_Source | VC_UC_Target | VC_UC_Same_Size       => "843",

           --  CWE-570 Expression is Always False

           when VC_Inconsistent_Pre
              | VC_Inconsistent_Post
              | VC_Inconsistent_Assume                              => "570",

           --  CWE-561 Dead Code

           when VC_Unreachable_Branch | VC_Dead_Code                => "561",

           --  We did not find a relevant CWE for the following yet

           when VC_Invariant_Check
              | VC_Invariant_Check_On_Default_Value
              | VC_Length_Check
              | VC_Ceiling_Interrupt
              | VC_Interrupt_Reserved
              | VC_Ceiling_Priority_Protocol
              | VC_Task_Termination
              | VC_Initial_Condition
              | VC_Default_Initial_Condition
              | VC_Disjoint_Cases
              | VC_Dynamic_Accessibility_Check
              | VC_Complete_Cases
              | VC_Loop_Invariant
              | VC_Loop_Invariant_Init
              | VC_Loop_Invariant_Preserv
              | VC_Subprogram_Variant
              | VC_Termination_Check
              | VC_Assert
              | VC_Assert_Premise
              | VC_Assert_Step
              | VC_Unexpected_Program_Exit
              | VC_Raise
              | VC_Reclamation_Check
              | VC_Feasible_Post
              | VC_Inline_Check
              | VC_Container_Aggr_Check
              | VC_Weaker_Pre
              | VC_Trivial_Weaker_Pre
              | VC_Stronger_Post
              | VC_Weaker_Classwide_Pre
              | VC_Stronger_Classwide_Post
              | VC_Weaker_Pre_Access
              | VC_Stronger_Post_Access
              | VC_Null_Exclusion
              | VC_UC_Align_Overlay
              | VC_UC_Align_UC
              | VC_Unchecked_Union_Restriction
              | VC_UC_Volatile
              | VC_Validity_Check                                   => "");
   end CWE_ID;

   function CWE_ID (Kind : Valid_Flow_Tag_Kind) return String is
   begin
      return
        (case Kind is
           --  CWE-561: Dead Code

           when Dead_Code                                       => "561",

           --  CWE-362: Concurrent Execution using Shared Resource with
           --  Improper Synchronization ('Race Condition')

           when Concurrent_Access                               => "362",

           --  CWE-457: Use of Uninitialized Variable

           when Default_Initialization_Mismatch | Uninitialized => "457",

           --  CWE-667: Improper Locking

           when Potentially_Blocking_In_Protected               => "667",

           --  CWE-563: Assignment to Variable without Use ('Unused Variable')

           when Unused_Initial_Value | Unused_Variable          => "563",

           --  CWE-1164: Irrelevant Code

           when Ineffective                                     => "1164",

           --  CWE-674: Uncontrolled Recursion

           when Call_In_Type_Invariant | Subprogram_Termination => "674",

           when Aliasing
              | Call_To_Current_Task
              | Critical_Global_Missing
              | Depends_Null
              | Depends_Missing
              | Depends_Missing_Clause
              | Depends_Wrong
              | Export_Depends_On_Proof_In
              | Ghost_Wrong
              | Global_Missing
              | Global_Wrong
              | Hidden_Unexposed_State
              | Illegal_Update
              | Impossible_To_Initialize_State
              | Initializes_Wrong
              | Inout_Only_Read
              | Missing_Return
              | Non_Volatile_Function_With_Volatile_Effects
              | Not_Constant_After_Elaboration
              | Reference_To_Non_CAE_Variable
              | Refined_State_Wrong
              | Side_Effects
              | Stable
              | Unused_Global
              | Volatile_Function_Without_Volatile_Effects      => "");
   end CWE_ID;

   -----------------
   -- CWE_Message --
   -----------------

   function CWE_Message (Kind : VC_Kind) return String
   is (Wrap_CWE (CWE_ID (Kind)));

   function CWE_Message (Kind : Valid_Flow_Tag_Kind) return String
   is (Wrap_CWE (CWE_ID (Kind)));

   -----------------
   -- Description --
   -----------------

   pragma Annotate (Xcov, Exempt_On, "Not called from gnat2why");

   function Description (Kind : VC_Kind) return String is
   begin
      case Kind is
         when VC_Division_Check                   =>
            return
              "Check that the second operand of the division, mod or "
              & "rem operation is different from zero.";

         when VC_Index_Check                      =>
            return
              "Check that the given index is within the bounds of "
              & "the array.";

         when VC_Overflow_Check                   =>
            return
              "Check that the result of the given integer arithmetic "
              & "operation is within the bounds of the base type.";

         when VC_FP_Overflow_Check                =>
            return
              "Check that the result of the given floating point "
              & "operation is within the bounds of the base type.";

         when VC_Range_Check                      =>
            return
              "Check that the given value is within the bounds of the "
              & "expected scalar subtype.";

         when VC_Predicate_Check                  =>
            return
              "Check that the given value respects the applicable type "
              & "predicate.";

         when VC_Predicate_Check_On_Default_Value =>
            return
              "Check that the default value for the type respects the "
              & "applicable type predicate.";

         when VC_Null_Pointer_Dereference         =>
            return
              "Check that the given pointer is not null so that it can "
              & "be dereferenced.";

         when VC_Null_Exclusion                   =>
            return
              "Check that the subtype_indication of the allocator "
              & "does not specify a null_exclusion";

         when VC_Dynamic_Accessibility_Check      =>
            return
              "Check that the accessibility level of the result of a "
              & "traversal function call is not deeper than the accessibility "
              & "level of its traversed parameter.";

         when VC_Resource_Leak                    =>
            return
              "Check that the assignment does not lead to a resource"
              & " or memory leak";

         when VC_Resource_Leak_At_End_Of_Scope    =>
            return
              "Check that the declaration does not lead to a resource"
              & " or memory leak";

         when VC_Invariant_Check                  =>
            return
              "Check that the given value respects the applicable type "
              & "invariant.";

         when VC_Invariant_Check_On_Default_Value =>
            return
              "Check that the default value for the type respects the "
              & "applicable type invariant.";

         when VC_Length_Check                     =>
            return
              "Check that the given array is of the length of the "
              & "expected array subtype.";

         when VC_Discriminant_Check               =>
            return
              "Check that the discriminant of the given discriminated "
              & "record has the expected value. For variant records, this can "
              & "happen for a simple access to a record field. But there are "
              & "other cases where a fixed value of the discriminant is "
              & "required.";

         when VC_Tag_Check                        =>
            return
              "Check that the tag of the given tagged object has the "
              & "expected value.";

         when VC_Loop_Variant                     =>
            return
              "Check that the given loop variant decreases/increases "
              & "as specified during each iteration of the loop. This "
              & "implies termination of the loop.";

         when VC_Subprogram_Variant               =>
            return
              "Check that the given subprogram variant decreases/"
              & "increases as specified during each recursive call. This "
              & "implies there will be no infinite recursion.";

         when VC_Termination_Check                =>
            return
              "Check the termination of subprograms annotated with"
              & " an Always_Terminates aspect whose value is not known at "
              & "compile time and of calls to such subprograms.";

         when VC_Ceiling_Interrupt                =>
            return
              "Check that the ceiling priority specified for a "
              & "protected object containing a procedure with an aspect "
              & "Attach_Handler is in Interrupt_Priority.";

         when VC_Interrupt_Reserved               =>
            return
              "Check that the interrupt specified by Attach_Handler is "
              & "not reserved.";

         when VC_Ceiling_Priority_Protocol        =>
            return
              "Check that the ceiling priority protocol is respected, "
              & "i.e., when a task calls a protected operation, the active "
              & "priority of the task is not higher than the priority of the "
              & "protected object (Ada RM Annex D.3).";

         when VC_Task_Termination                 =>
            return
              "Check that the task does not terminate, as required by "
              & "Ravenscar.";

         when VC_Initial_Condition                =>
            return
              "Check that the initial condition of a package is true "
              & "after elaboration.";

         when VC_Default_Initial_Condition        =>
            return
              "Check that the default initial condition of a type is "
              & "true after default initialization of an object of the type.";

         when VC_Precondition                     =>
            return
              "Check that the precondition aspect of the given call "
              & "evaluates to True.";

         when VC_Precondition_Main                =>
            return
              "Check that the precondition aspect of the given main "
              & "procedure evaluates to True after elaboration.";

         when VC_Postcondition                    =>
            return
              "Check that the postcondition aspect of the subprogram "
              & "evaluates to True.";

         when VC_Refined_Post                     =>
            return
              "Check that the refined postcondition aspect of the "
              & "subprogram evaluates to True.";

         when VC_Contract_Case                    =>
            return
              "Check that all cases of the contract case evaluate to "
              & "true at the end of the subprogram.";

         when VC_Disjoint_Cases                   =>
            return
              "Check that the cases of the contract or exit cases"
              & " aspect are all mutually disjoint.";

         when VC_Complete_Cases                   =>
            return
              "Check that the cases of the contract cases aspect cover "
              & "the state space that is allowed by the precondition aspect.";

         when VC_Exceptional_Case                 =>
            return
              "Check that all cases of the exceptional cases evaluate "
              & "to true on exceptional exits.";

         when VC_Program_Exit_Post                =>
            return
              "Check that the program exit postcondition evaluates to "
              & "true when the program is exited.";

         when VC_Exit_Case                        =>
            return
              "Check that, for all cases of the exit cases, the exit "
              & "happens as specified.";

         when VC_Loop_Invariant                   =>
            return
              "Check that the loop invariant evaluates to True on all "
              & "iterations of the loop.";

         when VC_Loop_Invariant_Init              =>
            return
              "Check that the loop invariant evaluates to True on the "
              & "first iteration of the loop.";

         when VC_Loop_Invariant_Preserv           =>
            return
              "Check that the loop invariant evaluates to True at each "
              & "further iteration of the loop.";

         when VC_Assert                           =>
            return "Check that the given assertion evaluates to True.";

         when VC_Assert_Premise                   =>
            return
              "Check that the premise of an assertion with cut "
              & "operations evaluates to True.";

         when VC_Assert_Step                      =>
            return
              "Check that the side-condition of a cut operation "
              & "evaluates to True.";

         when VC_Raise                            =>
            return
              "Check that raise expressions can never be reached and "
              & "that all exceptions raised by raise statement and procedure "
              & "calls are expected.";

         when VC_Unexpected_Program_Exit          =>
            return
              "Check that a subprogram call cannot exit the whole "
              & "program.";

         when VC_Feasible_Post                    =>
            return
              "Check that an abstract function or access-to-function "
              & "type is feasible.";

         when VC_Inline_Check                     =>
            return
              "Check that an Annotate pragma with the Inline_For_Proof "
              & "or Logical_Equal identifier is correct.";

         when VC_Container_Aggr_Check             =>
            return
              "Check the invariants used to translate container "
              & "aggregates using the primitives provided by the Aggregate "
              & "aspect and the Container_Aggregates annotation.";

         when VC_Reclamation_Check                =>
            return
              "Check that confirming annotations on hidden types which "
              & "need reclamation are consistent with their full view.";

         when VC_UC_Source                        =>
            return
              "Check that a source type in an unchecked conversion can "
              & "safely be used for such conversions. This means that the "
              & "memory occupied by objects of this type is fully used by the "
              & "object.";

         when VC_UC_Target                        =>
            return
              "Check that a target type in an unchecked conversion can "
              & "safely be used for such conversions. This means that the "
              & "memory occupied by objects of this type is fully used by the "
              & "object, and no invalid bitpatterns occur.";

         when VC_UC_Same_Size                     =>
            return
              "Check that the two types in an unchecked conversion "
              & "instance are of the same size.";

         when VC_UC_Align_Overlay                 =>
            return
              "Check that the address within address clause is "
              & "a multiple of the object's alignment.";

         when VC_UC_Align_UC                      =>
            return
              "Check that the alignment of the source of the unchecked "
              & "conversion is a multiple of the alignment of the target.";

         when VC_UC_Volatile                      =>
            return
              "Check that, if an object has an address clause that is "
              & "not simply the address of another object, it is volatile";

         when VC_Weaker_Pre                       =>
            return
              "Check that the precondition aspect of the subprogram is "
              & "weaker than its class-wide precondition.";

         when VC_Trivial_Weaker_Pre               =>
            return
              "Check that the precondition aspect of the subprogram is "
              & "True if its class-wide precondition is True.";

         when VC_Stronger_Post                    =>
            return
              "Check that the postcondition aspect of the subprogram "
              & "is stronger than its class-wide postcondition.";

         when VC_Weaker_Classwide_Pre             =>
            return
              "Check that the class-wide precondition aspect of the "
              & "subprogram is weaker than its overridden class-wide "
              & "precondition.";

         when VC_Stronger_Classwide_Post          =>
            return
              "Check that the class-wide postcondition aspect of the "
              & "subprogram is stronger than its overridden class-wide "
              & "postcondition.";

         when VC_Weaker_Pre_Access                =>
            return
              "Check that the precondition aspect of the"
              & " access-to-subprogram type used as the target of a conversion"
              & " implies the precondition of the source.";

         when VC_Stronger_Post_Access             =>
            return
              "Check that the postcondition aspect of the"
              & " access-to-subprogram type used as the target of a conversion"
              & " is implied by the postcondition of the source.";

         when VC_Inconsistent_Pre                 =>
            return "Warn if precondition is found to be always False";

         when VC_Inconsistent_Post                =>
            return "Warn if postcondition is found to be always False";

         when VC_Inconsistent_Assume              =>
            return "Warn if pragma Assume is found to be always False";

         when VC_Unreachable_Branch               =>
            return "Warn if branch is found to be unreachable";

         when VC_Dead_Code                        =>
            return "Warn if code is found to be unreachable";

         when VC_Initialization_Check             =>
            return "Check that a variable is initialized";

         when VC_Validity_Check                   =>
            return "Check that no invalid value is read";

         when VC_Unchecked_Union_Restriction      =>
            return
              "Check restrictions imposed on expressions of an unchecked"
              & " union type";
      end case;
   end Description;

   function Description (Kind : Valid_Flow_Tag_Kind) return String
   is (case Kind is
         when Aliasing                                    =>
           "Aliasing between formal parameters or global objects.",
         when Call_In_Type_Invariant                      =>
           "A type invariant calls a boundary subprogram for the type.",
         when Call_To_Current_Task                        =>
           "Current_Task is called from an invalid context.",
         when Concurrent_Access                           =>
           "An unsynchronized global object is accessed concurrently.",
         when Dead_Code                                   =>
           "A statement is never executed.",
         when Default_Initialization_Mismatch             =>
           "A type is wrongly declared as initialized by default.",
         when Depends_Missing                             =>
           "An input is missing from the dependency clause.",
         when Depends_Missing_Clause                      =>
           "An output item is missing from the dependency clause.",
         when Depends_Null                                =>
           "An input item is missing from the null dependency clause.",
         when Depends_Wrong                               =>
           "Extra input item in the dependency clause.",
         when Export_Depends_On_Proof_In                  =>
           "Subprogram output depends on a Proof_In global.",
         when Ghost_Wrong                                 =>
           "A ghost subprogram has a non-ghost global output.",
         when Critical_Global_Missing | Global_Missing    =>
           "A Global or Initializes contract fails to mention some objects.",
         when Global_Wrong                                =>
           "A Global or Initializes contract wrongly mentions some objects.",
         when Hidden_Unexposed_State                      =>
           "Constants with variable inputs that are not state constituents.",
         when Illegal_Update                              =>
           "Illegal write of a global input.",
         when Impossible_To_Initialize_State              =>
           "A state abstraction that is impossible to initialize.",
         when Ineffective                                 =>
           "A statement with no effect on subprogram's outputs.",
         when Initializes_Wrong                           =>
           "An object that shall not appear in the Initializes contract.",
         when Inout_Only_Read                             =>
           "An IN OUT parameter or an In_Out global that is not written.",
         when Missing_Return                              =>
           "All execution paths raise exceptions or do not return.",
         when Non_Volatile_Function_With_Volatile_Effects =>
           "A volatile function wrongly declared as non-volatile.",
         when Not_Constant_After_Elaboration              =>
           "Illegal write of an object "
           & "declared as constant after elaboration.",
         when Potentially_Blocking_In_Protected           =>
           "A protected operation may block.",
         when Reference_To_Non_CAE_Variable               =>
           "An illegal reference to global "
           & "in precondition of a protected operation.",
         when Refined_State_Wrong                         =>
           "Constant with no variable inputs "
           & "as an abstract state's constituent.",
         when Side_Effects                                =>
           "A function with side effects.",
         when Stable                                      =>
           "A loop with stable statement.",
         when Subprogram_Termination                      =>
           "A subprogram with aspect Always_Terminates may not terminate.",
         when Uninitialized                               =>
           "Flow analysis has detected the use of an uninitialized variable.",
         when Unused_Global                               =>
           "A global object is never used.",
         when Unused_Initial_Value                        =>
           "The initial value of an object is not used.",
         when Unused_Variable                             =>
           "A parameter or locally declared object is never used.",
         when Volatile_Function_Without_Volatile_Effects  =>
           "A non-volatile function wrongly declared as volatile.");

   function Description (Kind : Misc_Warning_Kind) return String
   is (case Kind is
         when Warn_Alias_Atomic_Vol                =>
           "aliased objects should both be volatile or non-volatile, "
           & "and both be atomic or non-atomic",
         when Warn_Alias_Different_Volatility      =>
           "aliased objects should have the same volatile properties",
         when Warn_Attribute_Valid                 =>
           "attribute Valid or Valid_Scalars is assumed to return True",
         when Warn_Auto_Lemma_Calls                =>
           "the automatically instantiated lemma contains calls which"
           & " cannot be arbitrarily specialized",
         when Warn_Auto_Lemma_Different            =>
           "the automatically instantiated lemma contains calls to its"
           & " associated function with different specializations",
         when Warn_Auto_Lemma_Higher_Order         =>
           "the automatically instantiated lemma is not annotated with"
           & " Higher_Order_Specialization",
         when Warn_Auto_Lemma_Specializable        =>
           "the automatically instantiated lemma does not contain any"
           & " specializable calls to its associated function",
         when Warn_Initialization_To_Alias         =>
           "initialization of object is assumed to have no effects on"
           & " other non-volatile objects",
         when Warn_Function_Is_Valid               =>
           "function Is_Valid is assumed to return True",
         when Warn_Generic_Not_Analyzed            =>
           "GNATprove doesn't analyze generics, only instances",
         when Warn_No_Possible_Termination         =>
           "procedure which does not return normally nor raises an exception"
           & " cannot always terminate",
         when Warn_Potentially_Invalid_Read        =>
           "invalid data might be read in the contract of a subprogram "
           & "without an analyzed body; the fact that the read data is valid "
           & "is not checked by SPARK",
         when Warn_Pragma_Annotate_No_Check        =>
           "no check message justified by this pragma",
         when Warn_Pragma_Annotate_Proved_Check    =>
           "only proved check messages justified by this pragma",
         when Warn_Pragma_Annotate_Terminating     =>
           "Terminating, Always_Return, and Might_Not_Return annotations are "
           & "ignored",
         when Warn_Pragma_External_Axiomatization  =>
           "External Axiomatizations are not supported anymore, ignored",
         when Warn_Pragma_Ignored                  =>
           "pragma is ignored (it is not yet supported)",
         when Warn_Pragma_Overflow_Mode            =>
           "pragma Overflow_Mode in code is ignored",
         when Warn_Precondition_Statically_False   =>
           "precondition is statically False",
         when Warn_Restriction_Ignored             =>
           "restriction is ignored (it is not yet supported)",
         when Warn_Unreferenced_Function           =>
           "analyzing unreferenced function",
         when Warn_Unreferenced_Procedure          =>
           "analyzing unreferenced procedure",
         when Warn_Useless_Potentially_Invalid_Obj =>
           "object annotated with Potentially_Invalid cannot have "
           & "invalid values",
         when Warn_Useless_Potentially_Invalid_Fun =>
           "function result annotated with Potentially_Invalid cannot have "
           & "invalid values",
         when Warn_Useless_Relaxed_Init_Fun        =>
           "function result annotated with Relaxed_Initialization cannot be"
           & " partially initialized",
         when Warn_Useless_Relaxed_Init_Obj        =>
           "object annotated with Relaxed_Initialization cannot be"
           & " partially initialized",
         when Warn_Variant_Not_Recursive           =>
           "no recursive call visible on subprogram with Subprogram_Variant",

         --  Warnings guaranteed to be issued
         when Warn_Address_To_Access               =>
           "call to conversion function is assumed to return a valid access"
           & " designating a valid value",
         when Warn_Assumed_Always_Terminates       =>
           "no Always_Terminates aspect available for subprogram, "
           & "subprogram is assumed to always terminate",
         when Warn_Assumed_Global_Null             =>
           "no Global contract available for subprogram, null is assumed",
         when Warn_Imprecisely_Supported_Address   =>
           "object with an imprecisely supported address specification: "
           & "non-atomic objects should not be accessed concurrently, "
           & "volatile properties should be correct, "
           & "indirect writes to object to and through potential aliases are "
           & "ignored, and "
           & "reads should be valid",

         --  Warnings enabled by --pedantic switch
         when Warn_Image_Attribute_Length          =>
           "string attribute has an implementation-defined length",
         when Warn_Operator_Reassociation          =>
           "possible operator reassociation due to missing parentheses",
         when Warn_Representation_Attribute_Value  =>
           "representation attribute has an implementation-defined value",

         --  Warnings enabled by --info switch
         when Warn_Unit_Not_SPARK                  =>
           "A unit whose analysis has been requested on the command-line is "
           & "not annotated with SPARK_Mode Pragma",

         --  Other tool limitations
         when Warn_Comp_Relaxed_Init               =>
           "If all components of a given type are annotated with "
           & " Relaxed_Initialization, the containing type is treated as if "
           & "it had the same annotation",
         when Warn_Full_View_Visible               =>
           "The full view of an incomplete type deferred to the body of a "
           & "withed unit might be visible by GNATprove",

         --  Flow limitations
         when Warn_Imprecise_GG                    =>
           "Global generation might wrongly classify an Output item as an "
           & "In_Out for subprograms that call other subprograms with no "
           & "Global contract",
         when Warn_Init_Array                      =>
           "Initialization of arrays inside FOR loops is only recognized when "
           & "assignments to array element are directly indexed by the loop"
           & "parameter",
         when Warn_Init_Multidim_Array             =>
           "Initialization of multi-dimensional array inside FOR loops is "
           & "only recognized when array bounds are static",
         when Warn_Alias_Array                     =>
           "Aliasing checks might be spurious for actual parameters that are "
           & "array components",
         when Warn_Tagged_Untangling               =>
           "Assignments to record objects might cause spurious data "
           & "dependencies in some components of the assigned object",

         --  Proof limitations
         when Warn_Contracts_Recursive             =>
           "Explicit and implicit postconditions of a recursive subprogram, "
           & "as well as the definition of a recursive expression function "
           & "with a numeric (not structural) Subprogram_Variant, might not "
           & "be available on (mutually) recursive calls occurring inside "
           & "assertions and contracts, but will still be available in "
           & "regular code",
         when Warn_Proof_Module_Cyclic             =>
           "A subprogram is part of a dependency cycle with other entities; "
           & "the explicit and implicit postconditions of mutually dependent "
           & "functions as well as their definition for recursive expression "
           & "functions cannot be used on "
           & "calls from these entities if they occur inside assertions and "
           & "contracts",
         when Warn_DIC_Ignored                     =>
           "The Default_Initial_Condition of a type won't be assumed on "
           & "subcomponents initialized by default inside assertions and "
           & "contracts, but will still be available in regular code",
         when Warn_Imprecise_Address               =>
           "The adress of objects is not precisely known if it is not "
           & "supplied through an address clause",
         when Warn_Imprecise_Align                 =>
           "The alignment of an object might not be known for proof if it is "
           & "not supplied through an attribute definition clause",
         when Warn_Imprecise_Call                  =>
           "The behavior of a call might not be known by SPARK and handled in "
           & "an imprecise way; its precondition might be impossible to prove "
           & "and nothing will be known about its result",
         when Warn_Imprecise_String_Literal        =>
           "The value of string literal containing wide characters or "
           & "constructed through the External_Initialization aspect is not "
           & "precisely known",
         when Warn_Component_Size                  =>
           "the value of attribute Component_Size might not be known for "
           & "proof if it is not supplied through an attribute definition "
           & "clause",
         when Warn_Record_Component_Attr           =>
           "the value of attributes First_Bit, Last_Bit, and Position on "
           & "record components are handled in an imprecise way if the record "
           & "does not have a record representation clause",
         when Warn_Imprecise_Size                  =>
           "The attributes Size, Object_Size or Value_Size might not be "
           & "handled precisely, nothing will be known about their evaluation",
         when Warn_Imprecise_UC                    =>
           "Unchecked conversion might not be handled precisely by SPARK, "
           & "nothing will be known about their result",
         when Warn_Imprecise_Overlay               =>
           "Overlay might not be handled precisely by SPARK, the value of "
           & "other overlaid objects will be unknown after an object is "
           & "updated",
         when Warn_Imprecise_Value                 =>
           "References to the attribute Value are handled in an imprecise "
           & "way; its precondition is impossible to prove and nothing will "
           & "be known about the evaluation of the attribute reference",
         when Warn_Imprecise_Image                 =>
           "References to the attributes Image and Img are handled in an "
           & "imprecise way; nothing will be known about the evaluation of the"
           & " attribute reference apart from a bound on its length",
         when Warn_Loop_Entity                     =>
           "The initial value of constants declared before the loop invariant "
           & "is not visible after the invariant; it shall be restated in the "
           & "invariant if necessary",
         when Warn_Init_Cond_Ignored               =>
           "The initial condition of a withed package might be ignored if it "
           & "is not known to be true, due to elaboration order",
         when Warn_No_Reclam_Func                  =>
           "No reclamation function or reclaimed value was found for an "
           & "ownership type, which may make it impossible to prove that "
           & "values of this type are reclaimed",
         when Warn_Map_Length_Aggregates           =>
           "A type with predefined map aggregates doesn't have a Length "
           & "function; the length of aggregates will not be known for "
           & "this type",
         when Warn_Set_Length_Aggregates           =>
           "A type with predefined set aggregates doesn't have a Length "
           & "function; the length of aggregates will not be known for "
           & "this type",
         when Warn_Relaxed_Init_Mutable_Discr      =>
           "The tool enforces that mutable discriminants of standalone objects"
           & " and parameters with relaxed initialization are always"
           & " initialized",
         when Warn_Predef_Eq_Null                  =>
           "A type is annotated with Only_Null as value for the "
           & "Predefined_Equality annotation, but no constant annotated with "
           & "Null_Value is found; this will result in all calls to the "
           & "predefined equality being rejected",

         --  Info messages enabled by default
         when Warn_Info_Unrolling_Inlining         =>
           "These messages are issued when the tool is unrolling loops or "
           & "inlining subprograms, or unable to do so");

   function Description (Kind : Unsupported_Kind) return String
   is (case Kind is
         when Lim_Abstract_State_Part_Of_Concurrent_Obj                   =>
           "an abstract state marked as Part_Of a concurrent object",
         when Lim_Access_Attr_With_Ownership_In_Unsupported_Context       =>
           "a reference to the ""Access"" attribute of an ownership type which"
           & " does not occur directly inside"
           & " an assignment statement, an object declaration, or a simple"
           & " return statement",
         when Lim_Access_Conv                                             =>
           "a conversion between access types with different "
           & "designated types",
         when Lim_Access_Sub_Protected                                    =>
           "an access-to-subprogram type designating a protected subprogram",
         when Lim_Access_Sub_Traversal                                    =>
           "an access-to-subprogram type designating a borrowing traversal"
           & " function",
         when Lim_Access_To_No_Return_Subp                                =>
           "an access-to-subprogram type designating a No_Return procedure",
         when Lim_Access_To_Relaxed_Init_Subp                             =>
           "an access-to-subprogram type designating a subprogram annotated"
           & " with Relaxed_Initialization",
         when Lim_Access_To_Subp_With_Exc                                 =>
           "access attribute on a procedure which might raise exceptions",
         when Lim_Access_To_Subp_With_Prog_Exit                           =>
           "access to procedure which might exit the program",
         when Lim_Address_Attr_In_Unsupported_Context                     =>
           "a reference to the ""Address"" attribute occuring within a "
           & "subtype indication, a range constraint, or a quantified"
           & " expression",
         when Lim_Alloc_With_Type_Constraints                             =>
           "an uninitialized allocator whose subtype indication has a type "
           & "constraint",
         when Lim_Array_Conv_Different_Size_Modular_Index                 =>
           "a conversion between array types if some matching index types"
           & " are modular types of different sizes",
         when Lim_Array_Conv_Signed_Modular_Index                         =>
           "a conversion between array types if some matching index types"
           & " are not both signed or both modular",
         when Lim_Assert_And_Cut_Meet_Inv                                 =>
           "a pragma Assert_And_Cut occurring immediately within a sequence"
           & " of statements containing a Loop_Invariant",
         when Lim_Borrow_Slice                                            =>
           "a borrow of a (part of) a slice",
         when Lim_Borrow_Traversal_First_Param                            =>
           "a borrowing traversal function whose first formal parameter does"
           & " not have an anonymous access-to-variable type",
         when Lim_Borrow_Traversal_Volatile                               =>
           "a borrowing traversal function marked as a volatile function",
         when Lim_Class_Attr_Of_Constrained_Type                          =>
           "a reference to the ""Class"" attribute on a constrained type",
         when Lim_Classwide_Representation_Value                          =>
           "a representation attribute on an object of classwide type",
         when Lim_Classwide_With_Predicate                                =>
           "a subtype predicate on a classwide type",
         when Lim_Complex_Raise_Expr_In_Prec                              =>
           "a raise expression occurring in a precondition, unless it is only"
           & " used to change the reported error and can safely be "
           & "interpreted as False",
         when Lim_Continue_Cross_Inv                                      =>
           "a continue statement preceding loop-invariant",
         when Lim_Constrained_Classwide                                   =>
           "a type constraint on a classwide subtype declaration",
         when Lim_Contract_On_Derived_Private_Type                        =>
           "a type contract (subtype predicate, default initial condition, or"
           & " type invariant) on a private type whose full view is another"
           & " private type",
         when Lim_Conv_Fixed_Float                                        =>
           "a conversion between a fixed-point type and a floating-point type",
         when Lim_Conv_Fixed_Integer                                      =>
           "a conversion between a fixed-point type and an integer type "
           & "when the small of the fixed-point type is neither an integer nor"
           & " the reciprocal of an integer",
         when Lim_Conv_Float_Modular_128                                  =>
           "a conversion between a floating point type and a modular type of"
           & " size 128",
         when Lim_Conv_Incompatible_Fixed                                 =>
           "a conversion between fixed point types whose smalls are not "
           & """compatible"" according to Ada RM G.2.3(21-24): the division of"
           & " smalls is not an integer or the reciprocal of an integer",
         when Lim_Cut_Operation_Context                                   =>
           "a call to the ""By"" or ""So"" function from the "
           & """SPARK.Cut_Operations"" library in an unsupported context",
         when Lim_Deep_Object_With_Addr                                   =>
           "an object with subcomponents of an access-to-variable type "
           & "annotated with an address clause whose value is the address of "
           & "another object",
         when Lim_Deep_Value_In_Delta_Aggregate                           =>
           "delta aggregate with possible aliasing of component associations "
           & "of an ownership type",
         when Lim_Derived_Interface                                       =>
           "interface derived from other interfaces",
         when Lim_Destructor                                              =>
           "record type with a destructors",
         when Lim_Entry_Family                                            =>
           "entry families",
         when Lim_Exceptional_Cases_Dispatch                              =>
           "aspect ""Exceptional_Cases"" on dispatching operations",
         when Lim_Exceptional_Cases_Ownership                             =>
           "procedure which might propagate exceptions with parameters of mode"
           & " ""in out"" or ""out"" subjected to ownership which might not "
           & "be passed by reference",
         when Lim_Exit_Cases_Dispatch                                     =>
           "aspect ""Exit_Cases"" on dispatching operations",
         when Lim_Program_Exit_Dispatch                                   =>
           "aspect ""Program_Exit"" on dispatching operations",
         when Lim_Program_Exit_Global_Modified_In_Callee                  =>
           "call which might exit the program and leave outputs "
           & "mentioned in the exit postcondition of its enclosing subprogram"
           & " in an inconsistent state",
         when Lim_Ext_Aggregate_With_Type_Ancestor                        =>
           "an extension aggregate whose ancestor part is a subtype mark",
         when Lim_Extension_Case_Pattern_Matching                         =>
           "GNAT extension for case pattern matching",
         when Lim_GNAT_Ext_Conditional_Goto                               =>
           "GNAT extension for conditional goto",
         when Lim_GNAT_Ext_Conditional_Raise                              =>
           "GNAT extension for conditional raise",
         when Lim_GNAT_Ext_Conditional_Return                             =>
           "GNAT extension for conditional return",
         when Lim_GNAT_Ext_Interpolated_String_Literal                    =>
           "GNAT extension for interpolated string literals",
         when Lim_Generic_In_Hidden_Private                               =>
           "instance of a generic unit declared in a package whose private "
           & "part is hidden outside of this package",
         when Lim_Generic_In_Type_Inv                                     =>
           "instance of a generic unit declared in a package containing a "
           & "type with an invariant outside of this package",
         when Lim_Goto_Cross_Inv                                          =>
           "a goto statement occuring in a loop before the invariant which"
           & " refers to a label occuring inside the loop but after the "
           & "invariant",
         when Lim_Hidden_Private_Relaxed_Init                             =>
           "private type whose full view contains only subcomponents whose "
           & "type is annotated with Relaxed_Initialization in a package "
           & "whose private part is hidden for proof",
         when Lim_Img_On_Non_Scalar                                       =>
           "a reference to the ""Image"" or ""Img"" attribute on a type or "
           & "an object of a type which is not a scalar type",
         when Lim_Incomplete_Type_Early_Usage                             =>
           "usage of incomplete type completed in package body outside of an "
           & "access type declaration",
         when Lim_Inherited_Controlling_Result_From_Hidden_Part           =>
           "a subprogram with dispatching result which is inherited,"
           & " not overriden, by a private extension completed in a hidden"
           & " private part",
         when Lim_Inherited_Controlling_Result_From_SPARK_Off             =>
           "a subprogram with dispatching result which is inherited,"
           & " not overriden, by a private extension completed in a private"
           & " part with SPARK_Mode Off",
         when Lim_Inherited_Prim_From_Hidden_Part                         =>
           "a subprogram which is inherited, not overriden, from an ancestor"
           & " declared in a hidden private part",
         when Lim_Inherited_Prim_From_SPARK_Off                           =>
           "a subprogram which is inherited, not overriden, from an ancestor"
           & " declared in the private part of a package with SPARK_Mode Off",
         when Lim_Iterated_Element_Association                            =>
           "container aggregates",
         when Lim_Iterator_In_Component_Assoc                             =>
           "an iterated component associations with an iterator specification"
           & " (""for ... of"") in an array aggregate",
         when Lim_Limited_Type_From_Limited_With                          =>
           "the use of an incomplete view of a type coming from a limited"
           & " with",
         when Lim_Loop_Inv_And_Handler                                    =>
           "a loop invariant in a list of statements with an exception "
           & "handler",
         when Lim_Loop_Inv_And_Finally                                    =>
           "a loop invariant in a list of statements with a finally section",
         when Lim_Loop_With_Iterator_Filter                               =>
           "a loop with an iterator filter in its parameter specification",
         when Lim_Max_Array_Dimension                                     =>
           "an array type with more than"
           & Max_Array_Dimensions'Img
           & " dimensions",
         when Lim_Max_Modulus                                             =>
           "a modular type with a modulus greater than 2 ** 128",
         when Lim_Move_To_Access_Constant                                 =>
           "a move operation occuring as part of  an allocator or a conversion"
           & " to an access-to-constant type which does not occur directly"
           & " inside an assignment statement, an object declaration, or a"
           & " simple return statement",
         when Lim_No_Return_Function                                      =>
           "a function annotated as No_Return",
         when Lim_Non_Static_Attribute                                    =>
           "a reference to a non-static attribute",
         when Lim_Multiple_Inheritance_Interfaces                         =>
           "a primitive operation which is inherited from several interfaces"
           & " in a tagged derivation",
         when Lim_Multiple_Inheritance_Mixed_SPARK_Mode                   =>
           "a primitive operation which is implicitly inherited from several"
           & " progenitor types in a tagged derivation, and for which two of"
           & " these progenitors provide incompatible values for the SPARK "
           & " mode of the inherited subprogram",
         when Lim_Multiple_Inheritance_Root                               =>
           "a primitive operation which is inherited both from the parent type"
           & " and from an interface in a tagged derivation",
         when Lim_Multidim_Iterator                                       =>
           "an iterator specification on a multidimensional array",
         when Lim_Multidim_Update                                         =>
           "a delta aggregate on a multidimensional array",
         when Lim_Null_Aggregate_In_Branching_Array_Aggregate             =>
           "a null aggregate which is a subaggregate of a multidimensional "
           & " array  aggregate with multiple associations",
         when Lim_Object_Before_Inv                                       =>
           "a non-scalar object or an object with an address clause declared"
           & " before the loop-invariant",
         when Lim_Op_Fixed_Float                                          =>
           "a multiplication or division between a fixed-point and a floating-"
           & "point value",
         when Lim_Op_Incompatible_Fixed                                   =>
           "a multiplication or division between different fixed-point types"
           & " if the result is not in the ""perfect result set"" according to"
           & " Ada RM G.2.3(21)",
         when Lim_Overlay_Uninitialized                                   =>
           "an object with an address clause which is not fully initialized "
           & "at declaration",
         when Lim_Overlay_With_Deep_Object                                =>
           "a reference to the ""Address"" attribute in an address clause"
           & " whose prefix has subcomponents of an access-to-variable type",
         when Lim_Deep_Object_Declaration_Outside_Block                   =>
           "a declaration of an object of an ownership type outside a block "
           & "for declarations",
         when Lim_Overriding_With_Precondition_Discrepancy_Hiding         =>
           "a dispatching primitive subprogram overriding with class-wide"
           & " precondition inherited from a potentially hidden ancestor",
         when Lim_Overriding_With_Precondition_Discrepancy_Tagged_Privacy =>
           "a dispatching primitive subprogram overriding declared for a"
           & " private untagged type with no specific precondition and a"
           & " class-wide precondition inherited from ancestor",
         when Lim_Potentially_Invalid_Eq                                  =>
           "the primitive equality of a record type with the "
           & "Potentially_Invalid aspect",
         when Lim_Potentially_Invalid_Iterable                            =>
           "a Potentially_Invalid aspect on a function associated to the"
           & " aspect Iterable",
         when Lim_Potentially_Invalid_Mutable_Discr                       =>
           "a part of potentially invalid object with mutable discriminants",
         when Lim_Potentially_Invalid_Part_Of                             =>
           "a potentially invalid object marked Part_Of a protected object",
         when Lim_Potentially_Invalid_Predicates                          =>
           "a potentially invalid object with a part subject to predicates",
         when Lim_Potentially_Invalid_Private                             =>
           "a potentially invalid object with a part whose full view is not in"
           & " SPARK",
         when Lim_Potentially_Invalid_Relaxed                             =>
           "a potentially invalid object with a part annotated with relaxed "
           & "initialization",
         when Lim_Potentially_Invalid_Subp_Access                         =>
           "an access to a subprogram annotated with Potentially_Invalid",
         when Lim_Potentially_Invalid_Traversal                           =>
           "a traversal function with a potentially invalid traversed "
           & "parameter",
         when Lim_Package_Before_Inv                                      =>
           "a package declaration occurring in a loop before the loop "
           & "invariant",
         when Lim_Predicate_With_Different_SPARK_Mode                     =>
           "a private type whose full view is not in SPARK annotated with two "
           & "subtype predicates, one on the full view and one on the partial "
           & "view",
         when Lim_Predicate_With_Different_Visibility                     =>
           "a private type declared in a package whose private part is hidden "
           & "for proof annotated with two subtype predicates, one on the "
           & "full view and one on the partial view",
         when Lim_Primitive_Call_In_DIC                                   =>
           "a call to a primitive operation of a tagged type T occurring in "
           & "the default initial condition of T with the type instance as a "
           & "parameter",
         when Lim_Protected_Operation_Of_Expression                       =>
           "a call to operation of a dereference",
         when Lim_Protected_Operation_Of_Component                        =>
           "a call to a protected operation of a protected component inside"
           & " a protected object",
         when Lim_Protected_Operation_Of_Formal                           =>
           "a call to a protected operation of the formal parameter of a"
           & " subprogram",
         when Lim_Refined_Post_On_Entry                                   =>
           "a protected entry annotated with a Refined_Post",
         when Lim_Relaxed_Init_Access_Type                                =>
           "an access-to-subprogram type used as a subcomponent of a type or"
           & " an object annotated with Relaxed_Initialization",
         when Lim_Relaxed_Init_Aliasing                                   =>
           "an object annotated with Relaxed_Initialization"
           & " is part of an overlay",
         when Lim_Relaxed_Init_Invariant                                  =>
           "a type annotated with an invariant used as a subcomponent of a"
           & " type or an object annotated with Relaxed_Initialization",
         when Lim_Relaxed_Init_Variant_Part                               =>
           "a subtype with a discriminant constraint containing only"
           & " subcomponents whose type is annotated with"
           & " Relaxed_Initialization",
         when Lim_Subprogram_Before_Inv                                   =>
           "a subprogram declaration occurring in a loop before the loop "
           & "invariant",
         when Lim_Subp_Variant_Eq                                         =>
           "a subprogram variant on the primitive equality of a record type",
         when Lim_Subp_Variant_Duplicate                                  =>
           "a subprogram with several Subprogram_Variant contracts",
         when Lim_Suspension_On_Expression                                =>
           "a call to a suspend operation on a dereference",
         when Lim_Suspension_On_Formal                                    =>
           "a call to a suspend operation on a suspension formal parameter",
         when Lim_Target_Name_In_Borrow                                   =>
           "an occurrence of the target name @ in an assignment to an object "
           & "of an anonymous access-to-variable type",
         when Lim_Target_Name_In_Move                                     =>
           "an occurrence of the target name @ in an assignment to an object "
           & "containing subcomponents of a named access-to-variable type",
         when Lim_Type_Inv_Access_Type                                    =>
           "an access type designating an incomplete or private type with a"
           & " subcomponent annotated with a type invariant",
         when Lim_Type_Inv_Protected_Type                                 =>
           "a protected type annotated with a type invariant",
         when Lim_Type_Inv_Tagged_Comp                                    =>
           "a tagged type with a subcomponent annotated with a type invariant",
         when Lim_Type_Inv_Tagged_Type                                    =>
           "a tagged type annotated with a type invariant",
         when Lim_Type_Inv_Volatile                                       =>
           "a volatile object with asynchronous writers or readers and a type"
           & " invariant",
         when Lim_Uninit_Alloc_In_Expr_Fun                                =>
           "an uninitialized allocator inside an expression function",
         when Lim_Unknown_Alignment                                       =>
           "a reference to the ""Alignment"" attribute on a prefix which is "
           & "not a type with an alignment clause",
         when Lim_Unknown_Size                                            =>
           "a reference to the ""Size"" attribute on a prefix which is "
           & "not a standalone object, a formal parameter, a component, or "
           & "a slice with no padding",
         when Lim_UU_Tagged_Comp                                          =>
           "a component of an unconstrained unchecked union type in a tagged "
           & "extension",
         when Lim_Indexed_Container_Aggregate                             =>
           "an indexed container aggregate");

   pragma Annotate (Xcov, Exempt_Off);

   -------------------
   -- Error_Message --
   -------------------

   function Error_Message (Kind : Error_Message_Kind) return String is
   begin
      case Kind is
         when Err_Comp_Not_Present =>
            return "component not present in &";

         when Marking_Error_Kind   =>
            raise Program_Error;
      end case;
   end Error_Message;

   ---------------
   -- From_JSON --
   ---------------

   function From_JSON (V : JSON_Value) return Prover_Stat is
   begin
      return
        Prover_Stat'
          (Count     => Get (Get (V, "count")),
           Max_Steps => Get (Get (V, "max_steps")),
           Max_Time  => Get (Get (V, "max_time")));
   end From_JSON;

   function From_JSON (V : JSON_Value) return Prover_Stat_Maps.Map is

      Map : Prover_Stat_Maps.Map;

      procedure Process_Prover_Stat (Name : UTF8_String; Value : JSON_Value);

      -------------------------
      -- Process_Prover_Stat --
      -------------------------

      procedure Process_Prover_Stat (Name : UTF8_String; Value : JSON_Value) is
      begin
         Map.Insert (Name, From_JSON (Value));
      end Process_Prover_Stat;

      --  Start of processing for From_Json

   begin
      Map_JSON_Object (V, Process_Prover_Stat'Access);
      return Map;
   end From_JSON;

   pragma Annotate (Xcov, Exempt_On, "Not called from gnat2why");
   function From_JSON (V : JSON_Value) return Prover_Category is
      S : constant String := Get (V);
   begin
      if S = "trivial" then
         return PC_Trivial;
      elsif S = "prover" then
         return PC_Prover;
      elsif S = "flow" then
         return PC_Flow;
      end if;
      raise Program_Error;
   end From_JSON;
   pragma Annotate (Xcov, Exempt_Off);

   function From_JSON (V : JSON_Value) return CEE_Kind is
      S : constant String := Get (V);
   begin
      if S = "variable" then
         return CEE_Variable;
      elsif S = "error_message" then
         return CEE_Error_Msg;
      elsif S = "old" then
         return CEE_Old;
      elsif S = "before_loop" then
         return CEE_Other; -- CEE_Before_Loop;
      elsif S = "current_iteration" then
         return CEE_Other; -- CEE_Current_Iteration;
      elsif S = "before_iteration" then
         return CEE_Other; -- CEE_Previous_Iteration
      elsif S = "result" then
         return CEE_Result;
      elsif S = "other" then
         return CEE_Other;
      elsif S'Length > 1 and then S (S'First) = '@' then
         return CEE_Other; -- CEE_At
      end if;
      raise Program_Error;
   end From_JSON;

   function From_JSON (V : JSON_Value) return Cntexample_File_Maps.Map is

      Map : Cntexample_File_Maps.Map;
      Ar  : constant JSON_Array :=
        (if Is_Empty (V) then Empty_Array else Get (V));

   begin
      for Var_Index in Positive range 1 .. Length (Ar) loop
         declare
            Elt : constant JSON_Value := Get (Ar, Var_Index);
         begin
            Map.Insert (Get (Elt, "filename"), From_JSON (Get (Elt, "model")));
         end;
      end loop;
      return Map;
   end From_JSON;

   function From_JSON (V : JSON_Value) return Cntexample_Lines is

      Ar  : constant JSON_Array := Get (V);
      Res : Cntexample_Lines :=
        Cntexample_Lines'
          (VC_Line        => Cntexample_Elt_Lists.Empty_List,
           Other_Lines    => Cntexample_Line_Maps.Empty_Map,
           Previous_Lines => Previous_Line_Maps.Empty_Map);

   begin
      for Var_Index in Positive range 1 .. Length (Ar) loop
         declare
            Elt        : constant JSON_Value := Get (Ar, Var_Index);
            Loc        : constant String := Get (Elt, "line");
            Is_VC_Line : constant Boolean := Get (Elt, "is_vc_line");
         begin
            if Is_VC_Line then
               Res.VC_Line := From_JSON ((Get (Elt, "model_elements")));
            else
               Res.Other_Lines.Insert
                 (Natural'Value (Loc),
                  From_JSON (Get (Elt, "model_elements")));
            end if;
         end;
      end loop;
      return Res;
   end From_JSON;

   function From_JSON (V : JSON_Value) return Cntexmp_Type is
      pragma Assert (Has_Field (V, "type"));
      T : constant String := Get (V, "type");
      E : constant Unbounded_String := To_Unbounded_String (T);

   begin
      if E = "Integer" then
         return Cnt_Integer;
      end if;

      if E = "Real" then
         return Cnt_Decimal;
      end if;

      if E = "Float" then
         return Cnt_Float;
      end if;

      if E = "Boolean" then
         return Cnt_Boolean;
      end if;

      if E = "BitVector" then
         return Cnt_Bitvector;
      end if;

      if E = "FunctionLiteral" then
         return Cnt_Array;
      end if;

      if E = "Record" then
         return Cnt_Record;
      end if;

      if E = "Proj" then
         return Cnt_Projection;
      end if;

      return Cnt_Invalid;
   end From_JSON;

   function From_JSON (V : JSON_Value) return Cntexample_Elt is
      Cnt_Value : constant Cntexmp_Value_Ptr :=
        new Cntexmp_Value'
          (Get_Typed_Cntexmp_Value
             (Get (Get (V, "value"), "value_concrete_term")));
   begin
      return
        Cntexample_Elt'
          (K      => Raw,
           Kind   => From_JSON (Get (V, "kind")),
           Name   => Get (Get (V, "name")),
           Labels => From_JSON_Labels (Get (Get (V, "attrs"))),
           Value  => Cnt_Value);
   end From_JSON;

   function From_JSON (V : JSON_Value) return Cntexample_Elt_Lists.List is
      Res : Cntexample_Elt_Lists.List := Cntexample_Elt_Lists.Empty_List;
      Ar  : constant JSON_Array :=
        (if Is_Empty (V) then Empty_Array else Get (V));
   begin
      for Var_Index in Positive range 1 .. Length (Ar) loop
         declare
            Elt : constant JSON_Value := Get (Ar, Var_Index);
         begin
            Res.Append (From_JSON (Elt));
         end;
      end loop;
      return Res;
   end From_JSON;

   function From_JSON (V : JSON_Value) return SPARK_Mode_Status is
      S : constant String := Get (V);
   begin
      return
        (if S = "all"
         then All_In_SPARK
         elsif S = "spec"
         then Spec_Only_In_SPARK
         elsif S = "no"
         then Not_In_SPARK
         else raise Program_Error);
   end From_JSON;

   function From_JSON (V : JSON_Value) return Warning_Status_Array is
      Result : Warning_Status_Array := Warning_Status;
   begin
      for MW in Misc_Warning_Kind loop
         Result (MW) :=
           Warning_Enabled_Status'Value
             (Get (Get (V, Misc_Warning_Kind'Image (MW))));
      end loop;
      return Result;
   end From_JSON;

   function From_JSON (V : JSON_Value) return GP_Mode
   is (GP_Mode'Value (Get (V)));

   ----------------------
   -- From_JSON_Labels --
   ----------------------

   function From_JSON_Labels (Ar : JSON_Array) return S_String_List.List is
      Res : S_String_List.List := S_String_List.Empty_List;
   begin
      for Var_Index in Positive range 1 .. Length (Ar) loop
         declare
            Elt : constant String := Get (Get (Ar, Var_Index));
         begin
            Res.Append (To_Unbounded_String (Elt));
         end;
      end loop;
      return Res;
   end From_JSON_Labels;

   --------------
   -- From_Tag --
   --------------

   function From_Tag (Tag : String) return Misc_Warning_Kind is
   begin
      for M in Misc_Warning_Kind loop
         if Tag = Kind_Name (M) then
            return M;
         end if;
      end loop;
      raise Constraint_Error;
   end From_Tag;

   -----------------------------
   -- Get_Typed_Cntexmp_Value --
   -----------------------------

   function Get_Typed_Cntexmp_Value (V : JSON_Value) return Cntexmp_Value is
      T : constant Cntexmp_Type := From_JSON (V);
   begin
      case T is
         when Cnt_Integer    =>
            return
              (T => Cnt_Integer, I => Get (Get (V, "val"), "int_verbatim"));

         when Cnt_Decimal    =>
            return
              (T => Cnt_Decimal, D => Get (Get (V, "val"), "real_verbatim"));

         --  Float values are complex so they are sent as JSON records. Example
         --  of values are infinities, zeroes, etc

         when Cnt_Float      =>
            declare
               Val        : constant JSON_Value := Get (V, "val");
               Float_Type : constant String := Get (Val, "float_type");
            begin
               if Float_Type = "Plus_infinity" then
                  return
                    (T => Cnt_Float,
                     F => new Float_Value'(F_Type => Float_Plus_Infinity));

               elsif Float_Type = "Minus_infinity" then
                  return
                    (T => Cnt_Float,
                     F => new Float_Value'(F_Type => Float_Minus_Infinity));

               elsif Float_Type = "Plus_zero" then
                  return
                    (T => Cnt_Float,
                     F => new Float_Value'(F_Type => Float_Plus_Zero));

               elsif Float_Type = "Minus_zero" then
                  return
                    (T => Cnt_Float,
                     F => new Float_Value'(F_Type => Float_Minus_Zero));

               elsif Float_Type = "Not_a_number" then
                  return
                    (T => Cnt_Float,
                     F => new Float_Value'(F_Type => Float_NaN));

               elsif Float_Type = "Float_value" then
                  return
                    (T => Cnt_Float,
                     F =>
                       new Float_Value'
                         (F_Type        => Float_Val,
                          F_Sign        =>
                            Get (Get (Val, "float_sign"), "bv_verbatim"),
                          F_Exponent    =>
                            Get (Get (Val, "float_exp"), "bv_verbatim"),
                          F_Significand =>
                            Get (Get (Val, "float_mant"), "bv_verbatim")));
               else
                  return (T => Cnt_Invalid, S => Null_Unbounded_String);
               end if;
            end;

         when Cnt_Boolean    =>
            return (T => Cnt_Boolean, Bo => Get (V, "val"));

         when Cnt_Bitvector  =>
            return
              (T => Cnt_Bitvector,
               B => Get (Get (V, "val"), "bv_value_as_decimal"));

         when Cnt_Record     =>
            declare
               Record_Val       : constant JSON_Array := Get (V, "val");
               Field_Value_List : Cntexmp_Value_Array.Map;

            begin

               for Index in 1 .. Length (Record_Val) loop
                  declare
                     Json_Element : constant JSON_Value :=
                       Get (Get (Record_Val, Index), "value");
                     Field_Name   : constant String :=
                       Get (Get (Record_Val, Index), "field");
                     Elem_Ptr     : constant Cntexmp_Value_Ptr :=
                       new Cntexmp_Value'
                         (Get_Typed_Cntexmp_Value (Json_Element));
                  begin
                     Field_Value_List.Insert (Field_Name, Elem_Ptr);
                  end;
               end loop;
               return (T => Cnt_Record, Fi => Field_Value_List);
            end;

         when Cnt_Projection =>
            --  All projections that gets to here should be removed. They are
            --  mostly to_reps.
            return
              Get_Typed_Cntexmp_Value (Get (Get (V, "val"), "proj_value"));

         when Cnt_Array      =>
            declare
               Array_Val       : constant JSON_Value := Get (V, "val");
               JS_Array_Elts   : constant JSON_Array :=
                 Get (Array_Val, "funliteral_elts");
               JS_Array_others : constant JSON_Value :=
                 Get (Array_Val, "funliteral_others");
               Indice_Array    : Cntexmp_Value_Array.Map;
               Other_Ptr       : Cntexmp_Value_Ptr;

            begin
               for Index in 1 .. Length (JS_Array_Elts) loop
                  declare
                     Json_Element : constant JSON_Value :=
                       Get (JS_Array_Elts, Index);

                  begin
                     declare
                        --  Indices are sent by Why3 as JSON model_value.
                        --  This is only accepted here if the model_value
                        --  is actually a simple value: integer, boolean...
                        --  And, on SPARK input, non simple value cannot
                        --  be produced.
                        Indice_Type : constant Cntexmp_Type :=
                          From_JSON (Get (Json_Element, "indice"));
                        Elem_Ptr    : constant Cntexmp_Value_Ptr :=
                          new Cntexmp_Value'
                            (Get_Typed_Cntexmp_Value
                               (Get (Json_Element, "value")));
                     begin
                        case Indice_Type is
                           when Cnt_Boolean   =>
                              Cntexmp_Value_Array.Insert
                                (Indice_Array,
                                 Get (Get (Json_Element, "indice"), "val"),
                                 Elem_Ptr);

                           when Cnt_Integer   =>
                              Cntexmp_Value_Array.Insert
                                (Indice_Array,
                                 Get
                                   (Get (Get (Json_Element, "indice"), "val"),
                                    "int_verbatim"),
                                 Elem_Ptr);

                           when Cnt_Decimal   =>
                              Cntexmp_Value_Array.Insert
                                (Indice_Array,
                                 Get
                                   (Get (Get (Json_Element, "indice"), "val"),
                                    "real_verbatim"),
                                 Elem_Ptr);

                           when Cnt_Bitvector =>
                              Cntexmp_Value_Array.Insert
                                (Indice_Array,
                                 Get
                                   (Get (Get (Json_Element, "indice"), "val"),
                                    "bv_value_as_decimal"),
                                 Elem_Ptr);

                           when others        =>
                              return
                                (T => Cnt_Invalid, S => Null_Unbounded_String);
                        end case;
                     end;

                  end;
               end loop;
               Other_Ptr :=
                 new Cntexmp_Value'(Get_Typed_Cntexmp_Value (JS_Array_others));
               if Other_Ptr = null then
                  Other_Ptr :=
                    new Cntexmp_Value'
                      (T => Cnt_Invalid, S => Null_Unbounded_String);

               end if;
               return
                 (T             => Cnt_Array,
                  Array_Indices => Indice_Array,
                  Array_Others  => Other_Ptr);
            end;

         when Cnt_Invalid    =>
            return (T => Cnt_Invalid, S => Null_Unbounded_String);
      end case;
   end Get_Typed_Cntexmp_Value;

   ---------------
   -- Kind_Name --
   ---------------

   pragma Annotate (Xcov, Exempt_On, "Not called from gnat2why");

   function Kind_Name (Kind : VC_Kind) return String is
   begin
      return
        (case Kind is
           when VC_Division_Check                   => "divide by zero",
           when VC_Index_Check                      => "index check",
           when VC_Overflow_Check                   => "overflow check",
           when VC_FP_Overflow_Check                => "fp_overflow check",
           when VC_Range_Check                      => "range check",
           when VC_Predicate_Check                  => "predicate check",
           when VC_Predicate_Check_On_Default_Value =>
             "predicate check on default value",
           when VC_Null_Pointer_Dereference         =>
             "null pointer dereference",
           when VC_Null_Exclusion                   => "null exclusion",
           when VC_Dynamic_Accessibility_Check      =>
             "dynamic accessibility check",
           when VC_Resource_Leak                    =>
             "resource or memory leak",
           when VC_Resource_Leak_At_End_Of_Scope    =>
             "resource or memory leak at end of scope",
           when VC_Invariant_Check                  => "invariant check",
           when VC_Invariant_Check_On_Default_Value =>
             "invariant check on default value",
           when VC_Length_Check                     => "length check",
           when VC_Discriminant_Check               => "discriminant check",
           when VC_Tag_Check                        => "tag check",
           when VC_Ceiling_Interrupt                =>
             "ceiling priority in Interrupt_Priority",
           when VC_Interrupt_Reserved               => "interrupt is reserved",
           when VC_Ceiling_Priority_Protocol        =>
             "ceiling priority protocol",
           when VC_Task_Termination                 => "task termination",
           when VC_Initial_Condition                => "initial condition",
           when VC_Default_Initial_Condition        =>
             "default initial condition",
           when VC_Precondition                     => "precondition",
           when VC_Precondition_Main                => "precondition of main",
           when VC_Postcondition                    => "postcondition",
           when VC_Refined_Post                     => "refined postcondition",
           when VC_Contract_Case                    => "contract case",
           when VC_Disjoint_Cases                   =>
             "disjoint contract or exit cases",
           when VC_Complete_Cases                   =>
             "complete contract cases",
           when VC_Exceptional_Case                 => "exceptional case",
           when VC_Program_Exit_Post                =>
             "program exit postcondition",
           when VC_Exit_Case                        => "exit case",
           when VC_Loop_Invariant                   => "loop invariant",
           when VC_Loop_Invariant_Init              =>
             "loop invariant in first iteration",
           when VC_Loop_Invariant_Preserv           =>
             "loop invariant after first iteration",
           when VC_Loop_Variant                     => "loop variant",
           when VC_Subprogram_Variant               => "subprogram variant",
           when VC_Termination_Check                => "termination check",
           when VC_Assert                           => "assertion",
           when VC_Assert_Premise                   => "assertion premise",
           when VC_Assert_Step                      => "assertion step",
           when VC_Raise                            => "raised exception",
           when VC_Unexpected_Program_Exit          =>
             "unexpected program exit",
           when VC_Feasible_Post                    => "feasible function",
           when VC_Inline_Check                     =>
             "Inline_For_Proof or Logical_Equal annotation",
           when VC_Container_Aggr_Check             =>
             "Container_Aggregates annotation",
           when VC_Reclamation_Check                =>
             "reclamation annotation",
           when VC_UC_Source                        =>
             "unchecked conversion source check",
           when VC_UC_Target                        =>
             "unchecked conversion target check",
           when VC_UC_Same_Size                     =>
             "unchecked conversion size check",
           when VC_UC_Align_Overlay                 =>
             "address alignment check",
           when VC_UC_Align_UC                      =>
             "unchecked conversion alignment check",
           when VC_UC_Volatile                      =>
             "volatile overlay check",
           when VC_Validity_Check                   => "validity check",
           when VC_Weaker_Pre                       =>
             "precondition weaker than class-wide precondition",
           when VC_Trivial_Weaker_Pre               =>
             "precondition not True while class-wide precondition is True",
           when VC_Stronger_Post                    =>
             "postcondition stronger than class-wide postcondition",
           when VC_Weaker_Classwide_Pre             =>
             "class-wide precondition weaker than overridden one",
           when VC_Stronger_Classwide_Post          =>
             "class-wide postcondition stronger than overridden one",
           when VC_Weaker_Pre_Access                =>
             "precondition of the source weaker than precondition of the"
             & " target",
           when VC_Stronger_Post_Access             =>
             "postcondition of the source stronger than postcondition of the"
             & " target",
           when VC_Inconsistent_Pre                 =>
             "precondition always False",
           when VC_Inconsistent_Post                =>
             "postcondition always False",
           when VC_Inconsistent_Assume              =>
             "pragma Assume always False",
           when VC_Unreachable_Branch               => "unreachable branch",
           when VC_Dead_Code                        => "unreachable code",
           when VC_Initialization_Check             =>
             "use of an uninitialized variable",
           when VC_Unchecked_Union_Restriction      =>
             "unchecked union restriction");
   end Kind_Name;

   function Kind_Name (Kind : Valid_Flow_Tag_Kind) return String
   is (case Kind is
         when Aliasing                                    =>
           "aliasing between subprogram parameters",
         when Call_In_Type_Invariant                      =>
           "invalid call in type invariant",
         when Call_To_Current_Task                        =>
           "invalid context for call to Current_Task",
         when Concurrent_Access                           => "race condition",
         when Critical_Global_Missing                     =>
           "critically incomplete Global or Initializes contract",
         when Dead_Code                                   => "dead code",
         when Default_Initialization_Mismatch             =>
           "wrong Default_Initial_Condition aspect",
         when Depends_Missing                             =>
           "input item missing from the dependency clause",
         when Depends_Missing_Clause                      =>
           "output item missing from the dependency clause",
         when Depends_Null                                =>
           "input item missing from the null dependency clause",
         when Depends_Wrong                               =>
           "extra input item in the dependency clause",
         when Export_Depends_On_Proof_In                  =>
           "subprogram output depends on a Proof_In global",
         when Ghost_Wrong                                 =>
           "non-ghost output of ghost subprogram",
         when Global_Missing                              =>
           "incomplete Global or Initializes contract",
         when Global_Wrong                                =>
           "an extra item in the Global or Initializes contract",
         when Hidden_Unexposed_State                      =>
           "constants with variable inputs that is not a state constituent",
         when Illegal_Update                              =>
           "illegal write of a global input",
         when Impossible_To_Initialize_State              =>
           "a state abstraction that is impossible to initialize",
         when Ineffective                                 =>
           "a statement with no effect on subprogram's outputs",
         when Initializes_Wrong                           =>
           "an extra item in the Initializes contract",
         when Inout_Only_Read                             =>
           "an IN OUT parameter or an In_Out global that is not written",
         when Missing_Return                              =>
           "all execution paths raise exceptions or do not return",
         when Non_Volatile_Function_With_Volatile_Effects =>
           "volatile function wrongly declared as non-volatile",
         when Not_Constant_After_Elaboration              =>
           "illegal write of an object "
           & "declared as constant after elaboration",
         when Potentially_Blocking_In_Protected           =>
           "protected operation blocks",
         when Reference_To_Non_CAE_Variable               =>
           "illegal reference to a global object "
           & "in precondition of a protected operation",
         when Refined_State_Wrong                         =>
           "constant with no variable inputs "
           & "as an abstract state's constituent",
         when Side_Effects                                =>
           "function with side effects",
         when Stable                                      =>
           "loop with stable statement",
         when Subprogram_Termination                      =>
           "subprogram with aspect Always_Terminates may not terminate",
         when Uninitialized                               =>
           "use of an uninitialized variable",
         when Unused_Global                               =>
           "global object is not used",
         when Unused_Initial_Value                        =>
           "initial value of an object is not used",
         when Unused_Variable                             =>
           "object is not used",
         when Volatile_Function_Without_Volatile_Effects  =>
           "non-volatile function wrongly declared as volatile");

   function Kind_Name (Kind : Misc_Warning_Kind) return String
   is (case Kind is
         when Warn_Alias_Atomic_Vol                =>
           "alias-volatile-atomic-mismatch",
         when Warn_Alias_Different_Volatility      =>
           "alias-volatile-prop-mismatch",
         when Warn_Attribute_Valid                 =>
           "attribute-valid-always-true",
         when Warn_Auto_Lemma_Calls                => "auto-lemma-calls",
         when Warn_Auto_Lemma_Different            => "auto-lemma-different",
         when Warn_Auto_Lemma_Higher_Order         =>
           "auto-lemma-higher-order",
         when Warn_Auto_Lemma_Specializable        =>
           "auto-lemma-specializable",
         when Warn_Initialization_To_Alias         =>
           "initialization-to-alias",
         when Warn_Function_Is_Valid               => "is-valid-returns-true",
         when Warn_Generic_Not_Analyzed            => "generic-not-analyzed",
         when Warn_No_Possible_Termination         =>
           "no-possible-termination",
         when Warn_Potentially_Invalid_Read        =>
           "potentially-invalid-read",
         when Warn_Pragma_Annotate_No_Check        =>
           "no-check-message-justified",
         when Warn_Pragma_Annotate_Proved_Check    => "proved-check-justified",
         when Warn_Pragma_Annotate_Terminating     => "deprecated-terminating",
         when Warn_Pragma_External_Axiomatization  =>
           "deprecated-external-axiomatization",
         when Warn_Pragma_Ignored                  => "ignored-pragma",
         when Warn_Pragma_Overflow_Mode            => "overflow-mode-ignored",
         when Warn_Precondition_Statically_False   =>
           "precondition-statically-false",
         when Warn_Restriction_Ignored             => "restriction-ignored",
         when Warn_Unreferenced_Function           => "unreferenced-function",
         when Warn_Unreferenced_Procedure          => "unreferenced-procedure",
         when Warn_Useless_Potentially_Invalid_Fun =>
           "useless-potentially-invalid-func-result",
         when Warn_Useless_Potentially_Invalid_Obj =>
           "useless-potentially-invalid-object",
         when Warn_Useless_Relaxed_Init_Fun        =>
           "useless-relaxed-init-func-result",
         when Warn_Useless_Relaxed_Init_Obj        =>
           "useless-relaxed-init-object",
         when Warn_Variant_Not_Recursive           => "variant-no-recursion",

         --  Warnings guaranteed to be issued
         when Warn_Address_To_Access               =>
           "address-to-access-conversion",
         when Warn_Imprecisely_Supported_Address   =>
           "imprecise-address-specification",
         when Warn_Assumed_Always_Terminates       =>
           "assumed-always-terminates",
         when Warn_Assumed_Global_Null             => "assumed-global-null",

         --  Warnings enabled by --pedantic switch
         when Warn_Image_Attribute_Length          => "image-attribute-length",
         when Warn_Operator_Reassociation          => "operator-reassociation",
         when Warn_Representation_Attribute_Value  =>
           "representation-attribute-value",

         --  Warnings enabled by --info switch
         when Warn_Alias_Array                     => "alias-array",
         when Warn_Comp_Relaxed_Init               => "component-relaxed-init",
         when Warn_Contracts_Recursive             => "contracts-recursive",
         when Warn_Proof_Module_Cyclic             => "cyclic-dependency",
         when Warn_DIC_Ignored                     => "dic-ignored",
         when Warn_Full_View_Visible               => "full-view-visible",
         when Warn_Imprecise_Address               => "imprecise-address",
         when Warn_Imprecise_Align                 => "imprecise-align",
         when Warn_Imprecise_Call                  => "imprecise-call",
         when Warn_Imprecise_GG                    =>
           "imprecise-global-generation",
         when Warn_Imprecise_String_Literal        =>
           "imprecise-string-literal",
         when Warn_Init_Array                      => "array-initialization",
         when Warn_Init_Multidim_Array             =>
           "multidimensional-array-init",
         when Warn_Component_Size                  =>
           "imprecise-component-size",
         when Warn_Record_Component_Attr           =>
           "imprecise-record-component-attribute",
         when Warn_Imprecise_Size                  => "imprecise-size",
         when Warn_Imprecise_Overlay               => "imprecise-overlay",
         when Warn_Imprecise_UC                    =>
           "imprecise-unchecked-conversion",
         when Warn_Imprecise_Value                 => "imprecise-value",
         when Warn_Imprecise_Image                 => "imprecise-image",
         when Warn_Loop_Entity                     => "constants-in-loops",
         when Warn_Init_Cond_Ignored               => "init-cond-ignored",
         when Warn_No_Reclam_Func                  =>
           "no-reclamation-function",
         when Warn_Map_Length_Aggregates           => "map-length-aggregates",
         when Warn_Set_Length_Aggregates           => "set-length-aggregates",
         when Warn_Relaxed_Init_Mutable_Discr      =>
           "relaxed-mutable-discriminants",
         when Warn_Tagged_Untangling               => "tagged-assignment",
         when Warn_Predef_Eq_Null                  =>
           "predefined-equality-null",
         when Warn_Unit_Not_SPARK                  => "unit-not-spark",

         --  Info messages enabled by default
         when Warn_Info_Unrolling_Inlining         =>
           "info-unrolling-inlining");

   pragma Annotate (Xcov, Exempt_Off);

   ---------------
   -- Rule_Name --
   ---------------

   function Rule_Name (Kind : VC_Kind) return String is
   begin
      return VC_Kind'Image (Kind);
   end Rule_Name;

   function Rule_Name (Kind : Valid_Flow_Tag_Kind) return String is
   begin
      return Valid_Flow_Tag_Kind'Image (Kind);
   end Rule_Name;

   -------------
   -- To_JSON --
   -------------

   function To_JSON (S : Prover_Stat) return JSON_Value is
      C : constant JSON_Value := Create_Object;
   begin
      Set_Field (C, "count", S.Count);
      Set_Field (C, "max_steps", S.Max_Steps);
      Set_Field (C, "max_time", S.Max_Time);
      return C;
   end To_JSON;

   function To_JSON (M : Prover_Stat_Maps.Map) return JSON_Value is
      Obj : constant JSON_Value := Create_Object;
   begin
      for C in M.Iterate loop
         Set_Field (Obj, Prover_Stat_Maps.Key (C), To_JSON (M (C)));
      end loop;
      return Obj;
   end To_JSON;

   function To_JSON (P : Prover_Category) return JSON_Value is
      S : constant String :=
        (case P is
           when PC_Prover  => "prover",
           when PC_Trivial => "trivial",
           when PC_Flow    => "flow");
   begin
      return Create (S);
   end To_JSON;

   function To_JSON (K : CEE_Kind) return JSON_Value is
      S : constant String :=
        (case K is
           when CEE_Old       => "old",
           when CEE_Result    => "result",
           when CEE_Variable  => "variable",
           when CEE_Error_Msg => "error_message",
           when CEE_Other     => "other");
   begin
      return Create (S);
   end To_JSON;

   function To_JSON (F : Cntexample_File_Maps.Map) return JSON_Value is
      Obj : constant JSON_Value := Create_Object;
   begin
      for C in F.Iterate loop
         Set_Field (Obj, Cntexample_File_Maps.Key (C), To_JSON (F (C)));
      end loop;
      return Obj;
   end To_JSON;

   function To_JSON (L : Cntexample_Lines) return JSON_Value is
      Obj      : constant JSON_Value := Create_Object;
      Obj_Prev : constant JSON_Value := Create_Object;
      Obj_Cur  : constant JSON_Value := Create_Object;

      function Line_Number_Image (L : Natural) return String;

      -----------------------
      -- Line_Number_Image --
      -----------------------

      function Line_Number_Image (L : Natural) return String is
         S : constant String := Natural'Image (L);
      begin
         return S (S'First + 1 .. S'Last);
      end Line_Number_Image;

      --  Start of processing for To_JSON

   begin
      Set_Field (Obj, "previous", Obj_Prev);
      Set_Field (Obj, "current", Obj_Cur);
      for C in L.Other_Lines.Iterate loop
         Set_Field
           (Obj_Cur,
            Line_Number_Image (Cntexample_Line_Maps.Key (C)),
            To_JSON (L.Other_Lines (C)));
      end loop;
      for C in L.Previous_Lines.Iterate loop
         Set_Field
           (Obj_Prev,
            Line_Number_Image (Previous_Line_Maps.Key (C)),
            To_JSON (L.Previous_Lines (C).Line_Cnt));
      end loop;
      return Obj;
   end To_JSON;

   function To_JSON (V : Cntexmp_Value) return JSON_Value is

      function Create_Float (F : Float_Value_Ptr) return JSON_Value;

      function Create_Record (A : Cntexmp_Value_Array.Map) return JSON_Value;

      function Create_Array
        (Indices : Cntexmp_Value_Array.Map; Other : Cntexmp_Value_Ptr)
         return JSON_Value;

      ------------------
      -- Create_Float --
      ------------------

      function Create_Float (F : Float_Value_Ptr) return JSON_Value is
         Res : constant JSON_Value := Create_Object;
      begin
         Set_Field (Res, "type", Float_Type'Image (F.F_Type));
         if F.F_Type = Float_Val then
            Set_Field (Res, "sign", To_String (F.F_Sign));
            Set_Field (Res, "exponend", To_String (F.F_Exponent));
            Set_Field (Res, "significand", To_String (F.F_Significand));
         end if;
         return Res;
      end Create_Float;

      -------------------
      -- Create_Record --
      -------------------

      function Create_Record (A : Cntexmp_Value_Array.Map) return JSON_Value is
         Res : constant JSON_Value := Create_Object;
         use Cntexmp_Value_Array;
      begin
         for C in A.Iterate loop
            Set_Field (Res, Key (C), To_JSON (A (C).all));
         end loop;
         return Res;
      end Create_Record;

      ------------------
      -- Create_Array --
      ------------------

      function Create_Array
        (Indices : Cntexmp_Value_Array.Map; Other : Cntexmp_Value_Ptr)
         return JSON_Value
      is
         Res : constant JSON_Value := Create_Object;
      begin
         Set_Field (Res, "indices", Create_Record (Indices));
         Set_Field (Res, "others", To_JSON (Other.all));
         return Res;
      end Create_Array;

      --  Start of processing for To_JSON

   begin
      return
        (case V.T is
           when Cnt_Integer    => Create (V.I),
           when Cnt_Decimal    => Create (V.D),
           when Cnt_Float      => Create_Float (V.F),
           when Cnt_Boolean    => Create (V.Bo),
           when Cnt_Bitvector  => Create (V.B),
           when Cnt_Record     => Create_Record (V.Fi),
           when Cnt_Projection => Create (V.Er),
           when Cnt_Array      =>
             Create_Array (V.Array_Indices, V.Array_Others),
           when Cnt_Invalid    => Create (V.S));
   end To_JSON;

   function To_JSON (C : Cntexample_Elt) return JSON_Value is
      Obj : constant JSON_Value := Create_Object;
   begin
      Set_Field (Obj, "name", C.Name);
      Set_Field (Obj, "kind", To_JSON (C.Kind));
      case C.K is
         when Raw            =>
            Set_Field (Obj, "type", Cntexmp_Type'Image (C.Value.T));
            Set_Field (Obj, "full_value", To_JSON (C.Value.all));

         when Pretty_Printed =>
            Set_Field (Obj, "value", C.Val_Str.Str);

         when Json_Format    =>
            Set_Field (Obj, "value", C.JSON_Obj);
      end case;
      return Obj;
   end To_JSON;

   function To_JSON (L : Cntexample_Elt_Lists.List) return JSON_Value is
      Result : JSON_Array := Empty_Array;
   begin
      for Elt of L loop
         Append (Result, To_JSON (Elt));
      end loop;
      return Create (Result);
   end To_JSON;

   function To_JSON (Status : SPARK_Mode_Status) return JSON_Value is
      S : constant String :=
        (case Status is
           when All_In_SPARK       => "all",
           when Spec_Only_In_SPARK => "spec",
           when Not_In_SPARK       => "no");
   begin
      return Create (S);
   end To_JSON;

   function To_JSON (S : Json_Formatted_Input) return JSON_Value is
      Obj : constant JSON_Value := Create_Object;
   begin
      Set_Field (Obj, "subp_file", S.File);
      Set_Field (Obj, "subp_line", S.Line);
      Set_Field (Obj, "inputs", To_JSON (S.Input_As_JSON));
      return Obj;
   end To_JSON;

   function To_JSON (M : GP_Mode) return JSON_Value is
   begin
      return Create (GP_Mode'Image (M));
   end To_JSON;

   function To_JSON (W : Warning_Status_Array) return JSON_Value is
      Obj : constant JSON_Value := Create_Object;
   begin
      for MW in Misc_Warning_Kind loop
         Set_Field
           (Obj,
            Misc_Warning_Kind'Image (MW),
            Warning_Enabled_Status'Image (W (MW)));
      end loop;
      return Obj;
   end To_JSON;

   ---------------
   -- To_String --
   ---------------

   function To_String (P : Prover_Category) return String is
   begin
      return
        (case P is
           when PC_Prover  => "Automatic provers",
           when PC_Trivial => "Trivial",
           when PC_Flow    => "Flow analysis");
   end To_String;

   function To_String (Code : Explain_Code_Kind) return String is
      Result : String := "0000";
      Rest   : Natural := Explain_Code_Kind'Enum_Rep (Code);
   begin
      for J in reverse Result'Range loop
         Result (J) := Character'Val (Character'Pos ('0') + Rest mod 10);
         Rest := Rest / 10;
      end loop;

      return 'E' & Result;
   end To_String;

   -----------------------
   -- Violation_Message --
   -----------------------

   function Violation_Message
     (Kind       : Violation_Kind;
      Name       : String := "";
      Root_Cause : Boolean := False) return String
   is (case Kind is
         when Vio_Access_Constant                          =>
           "Access attribute of a named access-to-constant type whose prefix "
           & "is not a constant part of an object",
         when Vio_Access_Expression                        =>
           "Access attribute on a complex expression",
         when Vio_Access_Function_With_Side_Effects        =>
           "access to function with side effects",
         when Vio_Access_No_Root                           =>
           "Access attribute of a path not rooted inside a parameter or "
           & "standalone object",
         when Vio_Access_Subprogram_Within_Protected       =>
           "access to subprogram declared within a protected object",
         when Vio_Access_Sub_Formal_With_Inv               =>
           "formal with type invariants in access-to-subprogram",
         when Vio_Access_Sub_Return_Type_With_Inv          =>
           "access-to-subprogram returning a type with invariants",
         when Vio_Access_Sub_With_Globals                  =>
           "access to subprogram with global effects",
         when Vio_Access_To_Dispatch_Op                    =>
           "access to dispatching operation",
         when Vio_Access_Volatile_Function                 =>
           "access to volatile function",
         when Vio_Address_Of_Non_Object                    =>
           "attribute ""Address"" of a non-object entity",
         when Vio_Address_Outside_Address_Clause           =>
           "attribute ""Address"" outside an attribute definition clause",
         when Vio_Assert_And_Cut_Context                   =>
           "pragma Assert_And_Cut outside a sequence of statements",
         when Vio_Backward_Goto                            =>
           "backward goto statement",
         when Vio_Box_Notation_Without_Init                =>
           "box notation without default or relaxed initialization",
         when Vio_Container_Aggregate                      =>
           "container aggregate whose type does not have the "
           & """Container_Aggregate"" annotation",
         when Vio_Code_Statement                           => "code statement",
         when Vio_Controlled_Types                         =>
           "controlled types",
         when Vio_Default_With_Current_Instance            =>
           "default expression with current instance of enclosing type",
         when Vio_Derived_Untagged_With_Tagged_Full_View   =>
           (if Root_Cause
            then "deriving from type declared as untagged private"
            else "deriving & from & declared as untagged private"),
         when Vio_Discriminant_Access                      =>
           "access discriminant",
         when Vio_Discriminant_Derived                     =>
           "discriminant on derived type",
         when Vio_Dispatch_Plain_Pre                       =>
           "plain precondition on dispatching subprogram",
         when Vio_Dispatching_Untagged_Type                =>
           "dispatching call on primitive of type with untagged partial view",
         when Vio_Exit_Cases_Exception                     =>
           "exit case mentioning exceptions when no exceptions can be "
           & "propagated",
         when Vio_Exit_Cases_Normal_Only                   =>
           "Exit_Case on subprogram which can only return normally",
         when Vio_Function_Global_Output                   =>
           "function with global outputs",
         when Vio_Function_Out_Param                       =>
           "function with ""out"" or ""in out"" parameters",
         when Vio_Ghost_Eq                                 =>
           "ghost function as user-defined equality on non-ghost record type",
         when Vio_Ghost_Concurrent_Comp                    =>
           (if Root_Cause
            then "concurrent component of ghost type"
            else "concurrent component & of ghost type &"),
         when Vio_Ghost_Volatile                           =>
           "volatile ghost object",
         when Vio_Handler_Choice_Parameter                 =>
           "choice parameter in handler",
         when Vio_Invariant_Class                          =>
           "classwide invariant",
         when Vio_Invariant_Ext                            =>
           "type invariant on completion of private_type_extension",
         when Vio_Invariant_Partial                        =>
           "type invariant on private_type_declaration or"
           & " private_type_extension",
         when Vio_Invariant_Volatile                       =>
           "type invariant on effectively volatile type",
         when Vio_Iterable_Controlling_Result              =>
           "function associated to aspect Iterable with controlling result",
         when Vio_Iterable_Full_View                       =>
           "Iterable aspect declared on the full view of a private type",
         when Vio_Iterable_Globals                         =>
           "function associated to aspect Iterable with dependency on globals",
         when Vio_Iterable_Side_Effects                    =>
           "function with side effects associated with aspect Iterable",
         when Vio_Iterable_Volatile                        =>
           "volatile function associated with aspect Iterable",
         when Vio_Iterator_Specification                   =>
           "iterator specification",
         when Vio_Loop_Variant_Structural                  =>
           "structural loop variant which is not a variable of an"
           & " anonymous access-to-object type",
         when Vio_Overlay_Constant_Not_Imported            =>
           "constant object with an address clause which is not imported",
         when Vio_Overlay_Mutable_Constant                 =>
           "mutable object and constant object overlaying each others",
         when Vio_Overlay_Part_Of_Protected                =>
           "overlaid object which is a part of a protected object",
         when Vio_Ownership_Access_Equality                =>
           "equality on access types",
         when Vio_Ownership_Allocator_Invalid_Context      =>
           "allocator or call to allocating function not stored in object "
           & "as part of assignment, declaration, or return statement",
         when Vio_Ownership_Allocator_Uninitialized        =>
           "uninitialized allocator without default initialization",
         when Vio_Ownership_Anonymous_Access_To_Named      =>
           "conversion from an anonymous access type to a named access "
           & "type",
         when Vio_Ownership_Anonymous_Part_Of              =>
           "anonymous access variable marked Part_Of a protected object",
         when Vio_Ownership_Anonymous_Object_Context       =>
           "object of anonymous access not declared "
           & "immediately within a subprogram, entry or block",
         when Vio_Ownership_Anonymous_Object_Init          =>
           "uninitialized object of anonymous access type",
         when Vio_Ownership_Anonymous_Result               =>
           "anonymous access type for result for non-traversal functions",
         when Vio_Ownership_Assign_To_Expr                 =>
           "assignment to a complex expression",
         when Vio_Ownership_Assign_To_Constant             =>
           "assignment into a constant object",
         when Vio_Ownership_Borrow_Of_Constant             =>
           "borrow of a constant object",
         when Vio_Ownership_Borrow_Of_Non_Markable         =>
           "borrow or observe of an expression which is not part of "
           & "stand-alone object or parameter",
         when Vio_Ownership_Anonymous_Component            =>
           "component of anonymous access type",
         when Vio_Ownership_Deallocate_General             =>
           "instance of Unchecked_Deallocation with a general access type",
         when Vio_Ownership_Different_Branches             =>
           "observe of a conditional or case expression with "
           & "branches rooted in different objects",
         when Vio_Ownership_Duplicate_Aggregate_Value      =>
           "duplicate value of a type with ownership",
         when Vio_Ownership_Loop_Entry_Old_Copy            =>
           "prefix of """
           & (if Root_Cause or else Name = ""
              then "Loop_Entry"" or ""Old"
              else Name)
           & """ attribute introducing aliasing",
         when Vio_Ownership_Loop_Entry_Old_Traversal       =>
           "traversal function call as a prefix of """
           & (if Root_Cause or else Name = ""
              then "Loop_Entry"" or ""Old"
              else Name)
           & """ attribute",
         when Vio_Ownership_Move_Constant_Part             =>
           "access-to-constant part of an object as source of move",
         when Vio_Ownership_Move_In_Declare                =>
           "move in declare expression",
         when Vio_Ownership_Move_Not_Name                  =>
           "expression as source of move",
         when Vio_Ownership_Move_Traversal_Call            =>
           "call to a traversal function as source of move",
         when Vio_Ownership_Reborrow                       =>
           "observed or borrowed expression which does not have the left-hand"
           & " side as a root",
         when Vio_Ownership_Storage_Pool                   =>
           "access type with Storage_Pool",
         when Vio_Ownership_Tagged_Extension               =>
           (if Root_Cause
            then "owning component of tagged extension"
            else "owning component & of tagged extension &"),
         when Vio_Ownership_Traversal_Extended_Return      =>
           "extended return applying to a traversal function",
         when Vio_Ownership_Volatile                       =>
           "observe, move, or borrow of volatile object",
         when Vio_Potentially_Invalid_Invariant            =>
           "potentially invalid object with a part subject to a type"
           & " invariant",
         when Vio_Potentially_Invalid_Dispatch             =>
           "dispatching operation with Potentially_Invalid aspect",
         when Vio_Potentially_Invalid_Overlay              =>
           "potentially invalid overlaid object",
         when Vio_Potentially_Invalid_Part_Access          =>
           "potentially invalid object with a part of an access type",
         when Vio_Potentially_Invalid_Part_Concurrent      =>
           "potentially invalid object with a part of a concurrent type",
         when Vio_Potentially_Invalid_Part_Tagged          =>
           "potentially invalid object with a part of a tagged type",
         when Vio_Potentially_Invalid_Part_Unchecked_Union =>
           "potentially invalid object with a part of an Unchecked_Union "
           & "type",
         when Vio_Potentially_Invalid_Scalar               =>
           "function returning a scalar that is not imported with "
           & "Potentially_Invalid aspect",
         when Vio_Predicate_Volatile                       =>
           "subtype predicate on effectively volatile type for reading",
         when Vio_Program_Exit_Outputs                     =>
           "output mentioned in the expression of an aspect Program_Exit "
           & "which is not a stand-alone objects",
         when Vio_Real_Root                                =>
           "expression of type root_real",
         when Vio_Relaxed_Init_Dispatch                    =>
           "dispatching operation with Relaxed_Initialization aspect",
         when Vio_Relaxed_Init_Initialized_Prefix          =>
           "attribute ""Initialized"" on a prefix which doesn't have "
           & "relaxed initialization",
         when Vio_Relaxed_Init_Part_Generic                =>
           "part of tagged, Unchecked_Union, or effectively volatile "
           & "object or type annotated with relaxed initialization",
         when Vio_Relaxed_Init_Part_Of_Tagged              =>
           "part of tagged type with relaxed Initialization",
         when Vio_Relaxed_Init_Part_Of_Unchecked_Union     =>
           "part of Unchecked_Union type with relaxed initialization",
         when Vio_Relaxed_Init_Part_Of_Volatile            =>
           "part of effectively volatile object or type annotated with "
           & "relaxed initialization",
         when Vio_Side_Effects_Call_Context                =>
           "call to a function with side effects outside of assignment or "
           & "object declaration without a block",
         when Vio_Side_Effects_Eq                          =>
           "function with side effects as user-defined equality on record "
           & "type",
         when Vio_Side_Effects_Traversal                   =>
           "traversal function with side effects",
         when Vio_Storage_Size                             =>
           "access type with Storage_Size",
         when Vio_Subp_Variant_Structural                  =>
           "structural subprogram variant which is not a parameter of the "
           & "subprogram",
         when Vio_Tagged_Extension_Local                   =>
           "local derived type from non-local parent or interface",
         when Vio_Target_Name_In_Call_With_Side_Effets     =>
           "use of ""@"" inside a call to a function with side effects",
         when Vio_Tasking_Synchronized_Comp                =>
           (if Root_Cause
            then "synchronized component of non-synchronized type"
            else "synchronized component & of non-synchronized type &"),
         when Vio_Tasking_Unintialized_Concurrent          =>
           "not fully initialized part of concurrent type",
         when Vio_Tasking_Unsupported_Construct            => "tasking",
         when Vio_UC_From_Access                           =>
           "unchecked conversion instance from a type with access"
           & " subcomponents",
         when Vio_UC_To_Access                             =>
           "unchecked conversion instance to an access type which is not a "
           & "general access-to-object type",
         when Vio_UC_To_Access_Components                  =>
           "unchecked conversion instance to a composite type with "
           & "access subcomponents",
         when Vio_UC_To_Access_From                        =>
           "unchecked conversion instance to an access-to-object type from "
           & "a type which is neither System.Address nor an integer type",
         when Vio_Unsupported_Attribute                    =>
           (if Root_Cause or else Name = ""
            then "unsupported attribute"
            else "attribute """ & Name & '"'),
         when Vio_Unsupported_Pragma                       =>
           (if Root_Cause then "unknown pragma" else "unknown pragma &"),
         when Vio_Volatile_At_Library_Level                =>
           "effectively volatile type or object not at library level",
         when Vio_Volatile_Discriminant                    =>
           "volatile discriminant",
         when Vio_Volatile_Discriminated_Type              =>
           "discriminated volatile type",
         when Vio_Volatile_Eq                              =>
           "volatile function as user-defined equality on record type",
         when Vio_Volatile_Global                          =>
           "nonvolatile function with volatile global inputs",
         when Vio_Volatile_In_Interferring_Context         =>
           "volatile object or volatile function call in interfering context",
         when Vio_Volatile_Incompatible_Comp               =>
           "component of composite type or designated type of an access with "
           & "an incompatible volatility",
         when Vio_Volatile_Incompatible_Type               =>
           "standalone object with an incompatible volatility with respect to "
           & "its type",
         when Vio_Volatile_Loop_Param                      =>
           "effectively volatile loop parameter",
         when Vio_Volatile_Parameter                       =>
           "nonvolatile function with effectively volatile parameter",
         when Vio_Volatile_Result                          =>
           "nonvolatile function with effectively volatile result");

   --------------
   -- Wrap_CWE --
   --------------

   function Wrap_CWE (S : String) return String is
   begin
      if S = "" then
         return "";
      else
         return " [CWE " & S & "]";
      end if;
   end Wrap_CWE;

end VC_Kinds;
