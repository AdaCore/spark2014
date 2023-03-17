------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                              V C _ K I N D S                             --
--                                                                          --
--                                 B o d y                                  --
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

package body VC_Kinds is

   function To_JSON (S : Prover_Stat)               return JSON_Value;
   function To_JSON (L : Cntexample_Lines)          return JSON_Value;
   function To_JSON (C : Cntexample_Elt)            return JSON_Value;
   function To_JSON (L : Cntexample_Elt_Lists.List) return JSON_Value;
   function To_JSON (K : CEE_Kind)                  return JSON_Value;

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

         when VC_Division_Check            => "369",

         --  CWE-119: Improper Restriction of Operations within the Bounds of a
         --  Memory Buffer.

         when VC_Index_Check               => "119",

         --  CWE-190: Integer Overflow or Wraparound

         when VC_Overflow_Check            => "190",

         --  CWE-739: CWE CATEGORY: CERT C Secure Coding Section 05 - Floating
         --  Point (FLP)

         when VC_FP_Overflow_Check         => "739",

         --  CWE-682: Incorrect Calculation

         when VC_Range_Check
            | VC_Predicate_Check
            | VC_Predicate_Check_On_Default_Value => "682",

         --  CWE-136: CWE CATEGORY: Type Errors

         when VC_Discriminant_Check
            | VC_Tag_Check                 => "136",

         --  CWE-835: Loop with Unreachable Exit Condition ('Infinite Loop')

         when VC_Loop_Variant              => "835",

         --  CWE-772: Missing Release of Resource after Effective Lifetime

         when VC_Resource_Leak
            | VC_Resource_Leak_At_End_Of_Scope => "772",

         --  CWE-476: NULL Pointer Dereference

         when VC_Null_Pointer_Dereference  => "476",

         --  CWE-457: Use of Uninitialized Variable

         when VC_Initialization_Check      => "457",

         --  CWE-628: Function Call with Incorrectly Specified Arguments

         when VC_Precondition
            | VC_Precondition_Main         => "628",

         --  CWE-682: Incorrect Calculation

         when VC_Postcondition
            | VC_Refined_Post
            | VC_Exceptional_Case
            | VC_Contract_Case             => "682",

         --  CWE-843 Access of Resource Using Incompatible Type ('Type
         --  Confusion')

         when VC_UC_Source
            | VC_UC_Target
            | VC_UC_Same_Size              => "843",

         --  CWE-570 Expression is Always False

         when VC_Inconsistent_Pre
            | VC_Inconsistent_Post
            | VC_Inconsistent_Assume       => "570",

         --  CWE-561 Dead Code

         when VC_Unreachable_Branch
            | VC_Dead_Code                 => "561",

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
            | VC_Disjoint_Contract_Cases
            | VC_Dynamic_Accessibility_Check
            | VC_Complete_Contract_Cases
            | VC_Loop_Invariant
            | VC_Loop_Invariant_Init
            | VC_Loop_Invariant_Preserv
            | VC_Subprogram_Variant
            | VC_Assert
            | VC_Assert_Premise
            | VC_Assert_Step
            | VC_Raise
            | VC_Feasible_Post
            | VC_Inline_Check
            | VC_Weaker_Pre
            | VC_Trivial_Weaker_Pre
            | VC_Stronger_Post
            | VC_Weaker_Classwide_Pre
            | VC_Stronger_Classwide_Post
            | VC_Weaker_Pre_Access
            | VC_Stronger_Post_Access
            | VC_Null_Exclusion
            | VC_UC_Alignment
            | VC_Unchecked_Union_Restriction
            | VC_UC_Volatile
         => "");
   end CWE_ID;

   function CWE_ID (Kind : Valid_Flow_Tag_Kind) return String is
   begin
      return
        (case Kind is
         --  CWE-561: Dead Code

         when Dead_Code                     => "561",

         --  CWE-362: Concurrent Execution using Shared Resource with Improper
         --  Synchronization ('Race Condition')

         when Concurrent_Access             => "362",

         --  CWE-457: Use of Uninitialized Variable

         when Default_Initialization_Mismatch
            | Uninitialized                 => "457",

         --  CWE-667: Improper Locking

         when Potentially_Blocking_In_Protected => "667",

         --  CWE-563: Assignment to Variable without Use ('Unused Variable')

         when Unused_Initial_Value
            | Unused_Variable               => "563",

         --  CWE-1164: Irrelevant Code

         when Ineffective                   => "1164",

         --  CWE-674: Uncontrolled Recursion

         when Call_In_Type_Invariant
            | Subprogram_Termination        => "674",

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
            | Volatile_Function_Without_Volatile_Effects => "");
   end CWE_ID;

   -----------------
   -- CWE_Message --
   -----------------

   function CWE_Message (Kind : VC_Kind) return String is
      (Wrap_CWE (CWE_ID (Kind)));

   function CWE_Message (Kind : Valid_Flow_Tag_Kind) return String is
      (Wrap_CWE (CWE_ID (Kind)));

   -----------------
   -- Description --
   -----------------

   pragma Annotate (Xcov, Exempt_On, "Not called from gnat2why");

   function Description (Kind : VC_Kind) return String is
   begin
      case Kind is
         when VC_Division_Check                   =>
            return "Check that the second operand of the division, mod or " &
              "rem operation is different from zero.";
         when VC_Index_Check                      =>
            return "Check that the given index is within the bounds of " &
              "the array.";
         when VC_Overflow_Check                   =>
            return "Check that the result of the given integer arithmetic " &
              "operation is within the bounds of the base type.";
         when VC_FP_Overflow_Check                =>
            return "Check that the result of the given floating point " &
              "operation is within the bounds of the base type.";
         when VC_Range_Check                      =>
            return "Check that the given value is within the bounds of the " &
              "expected scalar subtype.";
         when VC_Predicate_Check                  =>
            return "Check that the given value respects the applicable type " &
              "predicate.";
         when VC_Predicate_Check_On_Default_Value =>
            return "Check that the default value for the type respects the " &
              "applicable type predicate.";
         when VC_Null_Pointer_Dereference         =>
            return "Check that the given pointer is not null so that it can " &
              "be dereferenced.";
         when VC_Null_Exclusion                   =>
            return "Check that the subtype_indication of the allocator " &
              "does not specify a null_exclusion";
         when VC_Dynamic_Accessibility_Check      =>
            return "Check that the accessibility level of the result of a " &
              "traversal function call is not deeper than the accessibility " &
              "level of its traversed parameter.";
         when VC_Resource_Leak                    =>
            return "Check that the assignment does not lead to a resource"
              & " or memory leak";
         when VC_Resource_Leak_At_End_Of_Scope    =>
            return "Check that the declaration does not lead to a resource"
              & " or memory leak";
         when VC_Invariant_Check                  =>
            return "Check that the given value respects the applicable type " &
              "invariant.";
         when VC_Invariant_Check_On_Default_Value =>
            return "Check that the default value for the type respects the " &
              "applicable type invariant.";
         when VC_Length_Check                     =>
            return "Check that the given array is of the length of the " &
              "expected array subtype.";
         when VC_Discriminant_Check               =>
            return "Check that the discriminant of the given discriminated " &
              "record has the expected value. For variant records, this can " &
              "happen for a simple access to a record field. But there are " &
              "other cases where a fixed value of the discriminant is " &
              "required.";
         when VC_Tag_Check                        =>
            return "Check that the tag of the given tagged object has the " &
              "expected value.";
         when VC_Loop_Variant                     =>
            return "Check that the given loop variant decreases/increases " &
              "as specified during each iteration of the loop. This " &
              "implies termination of the loop.";
         when VC_Subprogram_Variant               =>
            return "Check that the given subprogram variant decreases/" &
              "increases as specified during each recursive call. This " &
              "implies there will be no infinite recursion.";
         when VC_Ceiling_Interrupt                =>
            return "Check that the ceiling priority specified for a " &
              "protected object containing a procedure with an aspect " &
              "Attach_Handler is in Interrupt_Priority.";
         when VC_Interrupt_Reserved               =>
            return "Check that the interrupt specified by Attach_Handler is " &
              "not reserved.";
         when VC_Ceiling_Priority_Protocol        =>
            return "Check that the ceiling priority protocol is respected, " &
              "i.e., when a task calls a protected operation, the active " &
              "priority of the task is not higher than the priority of the " &
              "protected object (Ada RM Annex D.3).";
         when VC_Task_Termination                 =>
            return "Check that the task does not terminate, as required by " &
              "Ravenscar.";
         when VC_Initial_Condition                =>
            return "Check that the initial condition of a package is true " &
              "after elaboration.";
         when VC_Default_Initial_Condition        =>
            return "Check that the default initial condition of a type is " &
              "true after default initialization of an object of the type.";
         when VC_Precondition                     =>
            return "Check that the precondition aspect of the given call " &
              "evaluates to True.";
         when VC_Precondition_Main                =>
            return "Check that the precondition aspect of the given main " &
              "procedure evaluates to True after elaboration.";
         when VC_Postcondition                    =>
            return "Check that the postcondition aspect of the subprogram " &
              "evaluates to True.";
         when VC_Refined_Post                     =>
            return "Check that the refined postcondition aspect of the " &
              "subprogram evaluates to True.";
         when VC_Contract_Case                    =>
            return "Check that all cases of the contract case evaluate to " &
              "true at the end of the subprogram.";
         when VC_Disjoint_Contract_Cases          =>
            return "Check that the cases of the contract cases aspect are " &
              "all mutually disjoint.";
         when VC_Complete_Contract_Cases          =>
            return "Check that the cases of the contract cases aspect cover " &
              "the state space that is allowed by the precondition aspect.";
         when VC_Exceptional_Case                 =>
            return "Check that all cases of the exceptional cases evaluate " &
              "to true on exceptional exits.";
         when VC_Loop_Invariant                   =>
            return "Check that the loop invariant evaluates to True on all " &
              "iterations of the loop.";
         when VC_Loop_Invariant_Init              =>
            return "Check that the loop invariant evaluates to True on the " &
              "first iteration of the loop.";
         when VC_Loop_Invariant_Preserv           =>
            return "Check that the loop invariant evaluates to True at each " &
              "further iteration of the loop.";
         when VC_Assert                           =>
            return "Check that the given assertion evaluates to True.";
         when VC_Assert_Premise                   =>
            return "Check that the premise of an assertion with cut " &
              "operations evaluates to True.";
         when VC_Assert_Step                      =>
            return "Check that the side-condition of a cut operation " &
              "evaluates to True.";
         when VC_Raise                            =>
            return "Check that raise expressions can never be reached and " &
              "that all exceptions raised by raise statement and procedure " &
              "calls are expected.";
         when VC_Feasible_Post                    =>
            return "Check that an abstract function or access-to-function " &
              "type is feasible.";
         when VC_Inline_Check                     =>
            return "Check that an Annotate pragma with the Inline_For_Proof " &
              "or Logical_Equal identifier is correct.";
         when VC_UC_Source                        =>
            return "Check that a source type in an unchecked conversion can " &
              "safely be used for such conversions. This means that the " &
              "memory occupied by objects of this type is fully used by the " &
              "object.";
         when VC_UC_Target                        =>
            return "Check that a target type in an unchecked conversion can " &
              "safely be used for such conversions. This means that the " &
              "memory occupied by objects of this type is fully used by the " &
              "object, and no invalid bitpatterns occur.";
         when VC_UC_Same_Size                     =>
            return "Check that the two types in an unchecked conversion " &
              "instance are of the same size.";
         when VC_UC_Alignment                     =>
            return "Check that the first object's alignment is an integral " &
              "multiple of the second object's alignment.";
         when VC_UC_Volatile                      =>
            return "Check that, if an object has an address clause that is " &
              "not simply the address of another object, it is volatile";
         when VC_Weaker_Pre                       =>
            return "Check that the precondition aspect of the subprogram is " &
              "weaker than its class-wide precondition.";
         when VC_Trivial_Weaker_Pre               =>
            return "Check that the precondition aspect of the subprogram is " &
              "True if its class-wide precondition is True.";
         when VC_Stronger_Post                    =>
            return "Check that the postcondition aspect of the subprogram " &
              "is stronger than its class-wide postcondition.";
         when VC_Weaker_Classwide_Pre             =>
            return "Check that the class-wide precondition aspect of the " &
              "subprogram is weaker than its overridden class-wide " &
              "precondition.";
         when VC_Stronger_Classwide_Post          =>
            return "Check that the class-wide postcondition aspect of the " &
              "subprogram is stronger than its overridden class-wide " &
              "postcondition.";
         when VC_Weaker_Pre_Access                =>
            return "Check that the precondition aspect of the"
              & " access-to-subprogram type used as the target of a conversion"
              & " implies the precondition of the source.";
         when VC_Stronger_Post_Access             =>
            return "Check that the postcondition aspect of the"
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
         when VC_Unchecked_Union_Restriction      =>
            return "Check restrictions imposed on expressions of an unchecked"
              & " union type";
      end case;
   end Description;

   function Description (Kind : Valid_Flow_Tag_Kind) return String is
     (case Kind is
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
            "A ghost procedure has a non-ghost global output.",
         when Critical_Global_Missing
            | Global_Missing                              =>
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
            "Illegal write of an object " &
            "declared as constant after elaboration.",
         when Potentially_Blocking_In_Protected =>
            "A protected operation may block.",
         when Reference_To_Non_CAE_Variable               =>
            "An illegal reference to global " &
            "in precondition of a protected operation.",
         when Refined_State_Wrong                         =>
            "Constant with no variable inputs " &
            "as an abstract state's constituent.",
         when Side_Effects                                =>
            "A function with side effects.",
         when Stable                                      =>
            "A loop with stable statement.",
         when Subprogram_Termination                      =>
            "A subprogram with Terminating annotation may not terminate.",
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

   function Description (Kind : Misc_Warning_Kind) return String is
     (case Kind is
        when Warn_Address_To_Access =>
          "call to conversion function is assumed to return a valid access"
          & " designating a valid value",
        when Warn_Alias_Atomic_Vol  =>
          "aliased objects should both be volatile or non-volatile, "
          & "and both be atomic or non-atomic",
        when Warn_Alias_Different_Volatility  =>
          "aliased objects should have the same volatile properties",
        when Warn_Attribute_Valid =>
          "attribute Valid is assumed to return True",
        when Warn_Initialization_To_Alias =>
          "initialization of object is assumed to have no effects on"
          & " other non-volatile objects",
        when Warn_Function_Is_Valid =>
          "function Is_Valid is assumed to return True",
        when Warn_Pragma_Annotate_No_Check =>
          "no check message justified by this pragma",
        when Warn_Pragma_Annotate_Proved_Check =>
          "only proved check messages justified by this pragma",
        when Warn_Pragma_Annotate_Terminating =>
          "Terminating annotations are deprecated",
        when Warn_Pragma_External_Axiomatization =>
          "External Axiomatizations are not supported anymore, ignored",
        when Warn_Pragma_Ignored =>
          "pragma is ignored (it is not yet supported)",
        when Warn_Pragma_Overflow_Mode =>
          "pragma Overflow_Mode in code is ignored",
        when Warn_Precondition_Statically_False =>
          "precondition is statically False",
        when Warn_Unreferenced_Function =>
          "analyzing unreferenced function",
        when Warn_Unreferenced_Procedure =>
          "analyzing unreferenced procedure",
        when Warn_Useless_Relaxed_Init_Fun =>
          "function result annotated with Relaxed_Initialization cannot be"
          & " partially initialized",
        when Warn_Useless_Relaxed_Init_Obj =>
          "object annotated with Relaxed_Initialization cannot be"
          & " partially initialized",
        when Warn_Useless_Always_Return_Fun =>
          "functions are implicitly annotated with Always_Return",
        when Warn_Useless_Always_Return_Lemma =>
          "automatically instantiated lemmas are implicitly annotated with"
           & " Always_Return",
        when Warn_Variant_Not_Recursive =>
          "no recursive call visible on subprogram with Subprogram_Variant",

        --  Warnings guaranteed to be issued
        when Warn_Address_Atomic =>
          "non-atomic object with an imprecisely supported address "
          & "specification should not be accessed concurrently",
        when Warn_Address_Valid =>
          "reads of an object with an imprecisely supported address "
          & "specification should be valid",
        when Warn_Assumed_Always_Return =>
          "no returning annotation available for subprogram, "
          & "subprogram is assumed to always return",
        when Warn_Assumed_Global_Null =>
          "no Global contract available for subprogram, null is assumed",
        when Warn_Assumed_Volatile_Properties =>
          "volatile properties of an object with an imprecisely supported "
          & "address specification should be correct",
        when Warn_Indirect_Writes_Through_Alias =>
          "indirect writes to object through a potential alias with an object"
          & " with an imprecisely supported address specification are ignored",
        when Warn_Indirect_Writes_To_Alias =>
          "writing to an object with an imprecisely supported address"
          & " specification is assumed to have no effects on other "
          & "non-volatile objects",

        --  Warnings only issued when using switch --pedantic
        when Warn_Image_Attribute_Length =>
          "string attribute has an implementation-defined length",
        when Warn_Operator_Reassociation =>
          "possible operator reassociation due to missing parentheses",
        when Warn_Representation_Attribute_Value =>
          "representation attribute has an implementation-defined value");

   function Description (Kind : Unsupported_Kind) return String is
     (case Kind is
         when Lim_Abstract_State_Part_Of_Concurrent_Obj =>
           "an abstract state marked as Part_Of a concurrent object",
         when Lim_Access_Attr_With_Ownership_In_Unsupported_Context =>
           "a reference to the ""Access"" attribute of an ownership type which"
          & " does not occur directly inside"
          & " an assignment statement, an object declaration, or a simple"
          & " return statement",
         when Lim_Access_Conv =>
           "an implicit conversion between access types with different "
          & "designated types",
         when Lim_Access_Sub_Formal_With_Inv =>
           "a formal parameter of an access-to-subprogram type which is"
          & " annotated with a type invariant",
         when Lim_Access_Sub_Protected =>
           "an access-to-subprogram type designating a protected subprogram",
         when Lim_Access_Sub_Return_Type_With_Inv =>
           "an access-to-subprogram type whose return type is annotated"
          & " with a type invariant",
         when Lim_Access_Sub_Traversal =>
           "an access-to-subprogram type designating a borrowing traversal"
          & " function",
         when Lim_Access_To_Dispatch_Op =>
           "an access-to-subprogram type designating a dispatching operation",
         when Lim_Access_To_Relaxed_Init_Subp =>
           "an access-to-subprogram type designating a subprogram annotated"
          & " with Relaxed_Initialization",
         when Lim_Address_Attr_In_Unsupported_Context =>
           "a reference to the ""Address"" attribute occuring within a "
          & "subtype indication, a range constraint, or a quantified"
          & " expression",
         when Lim_Array_Conv_Different_Size_Modular_Index =>
           "a conversion between array types if some matching index types"
          & " are modular types of different sizes",
         when Lim_Array_Conv_Signed_Modular_Index =>
           "a conversion between array types if some matching index types"
          & " are not both signed or both modular",
         when Lim_Borrow_Traversal_First_Param =>
           "a borrowing traversal function whose first formal parameter does"
          & " not have an anonymous access-to-variable type",
         when Lim_Borrow_Traversal_Volatile =>
           "a borrowing traversal function marked as a volatile function",
         when Lim_Class_Attr_Of_Constrained_Type =>
           "a reference to the ""Class"" attribute on a constrained type",
         when Lim_Classwide_With_Predicate =>
           "a subtype predicate on a classwide type",
         when Lim_Complex_Raise_Expr_In_Prec =>
           "a raise expression occurring in a precondition, unless it is only"
          & " used to change the reported error and can safely be interpreted "
          & "as False",
         when Lim_Constrained_Classwide =>
           "a type constraint on a classwide subtype declaration",
         when Lim_Contract_On_Derived_Private_Type =>
           "a type contract (subtype predicate, default initial condition, or"
          & " type invariant) on a private type whose full view is another"
          & " private type",
         when Lim_Conv_Fixed_Float =>
           "a conversion between a fixed-point type and a floating-point type",
         when Lim_Conv_Fixed_Integer =>
           "a conversion between a fixed-point type and an integer type "
          & "when the small of the fixed-point type is neither an integer nor"
          & " the reciprocal of an integer",
         when Lim_Conv_Float_Modular_128 =>
           "a conversion between a floating point type and a modular type of"
          & " size 128",
         when Lim_Conv_Incompatible_Fixed =>
           "a conversion between fixed point types whose smalls are not "
          & """compatible"" according to Ada RM G.2.3(21-24): the division of"
          & " smalls is not an integer or the reciprocal of an integer",
         when Lim_Deep_Object_With_Addr =>
           "an object with subcomponents of an access-to-variable type "
          & "annotated with an address clause whose value is the address of "
          & "another object",
         when Lim_Entry_Family => "entry families",
         when Lim_Exceptional_Cases_Dispatch =>
           "aspect ""Exceptional_Cases"" on dispatching operations",
         when Lim_Exceptional_Cases_Ownership =>
           "procedures with exceptional contracts and parameters of mode"
          & " ""in out"" or ""out"" subjected to ownerhsip which might not be "
          & "passed by reference",
         when Lim_Ext_Aggregate_With_Type_Ancestor =>
           "an extension aggregate whose ancestor part is a subtype mark",
         when Lim_Goto_Cross_Inv =>
           "a goto statement occuring in a loop before the invariant which"
          & " refers to a label occuring inside the loop but after the "
          & "invariant",
         when Lim_Img_On_Non_Scalar =>
           "a reference to the ""Image"" or ""Img"" attribute on a type or "
          & "an object of a type which is not a scalar type",
         when Lim_Interpolated_String_Literal =>
           "interpolated string literals",
         when Lim_Iterated_Element_Association => "container aggregates",
         when Lim_Iterator_In_Component_Assoc =>
           "an iterated component associations with an iterator specification"
          & " (""for ... of"") in an array aggregate",
         when Lim_Limited_Type_From_Limited_With =>
           "the use of an incomplete view of a type coming from a limited"
          & " with",
         when Lim_Loop_Inv_And_Handler =>
           "a loop invariant in a list of statements with an exception "
          & "handler",
         when Lim_Loop_With_Iterator_Filter =>
           "a loop with an iterator filter in its parameter specification",
         when Lim_Max_Array_Dimension =>
           "an array type with more than" & Max_Array_Dimensions'Img
          & " dimensions",
         when Lim_Max_Modulus =>
           "a modular type with a modulus greater than 2 ** 128",
         when Lim_Move_To_Access_Constant =>
           "a move operation occuring as part of a conversion to an "
          & "access-to-constant type",
         when Lim_No_Return_Function =>
           "a function annotated as No_Return",
         when Lim_Non_Static_Attribute =>
           "a reference to a non-static attribute",
         when Lim_Multiple_Inheritance_Interfaces =>
           "a primitive operation which is inherited from several interfaces"
          & " in a tagged derivation",
         when Lim_Multiple_Inheritance_Root =>
           "a primitive operation which is inherited both from the parent type"
          & " and from an interface in a tagged derivation",
         when Lim_Multidim_Iterator =>
           "an iterator specification on a multidimensional array",
         when Lim_Multidim_Update =>
           "a delta aggregate on a multidimensional array",
         when Lim_Object_Before_Inv =>
           "a non-scalar object declared in a loop before the loop invariant",
         when Lim_Op_Fixed_Float =>
           "a multiplication or division between a fixed-point and a floating-"
          & "point value",
         when Lim_Op_Incompatible_Fixed =>
           "a multiplication or division between different fixed-point types"
          & " if the result is not in the ""perfect result set"" according to"
          & " Ada RM G.2.3(21)",
         when Lim_Overlay_With_Deep_Object =>
           "a reference to the ""Address"" attribute in an address clause"
          & " whose prefix has subcomponents of an access-to-variable type",
         when Lim_Package_Before_Inv =>
           "a package declaration occurring in a loop before the loop "
          & "invariant",
         when Lim_Predicate_With_Different_SPARK_Mode =>
           "a private type whose full view is not in SPARK annotated with two"
          & " subtype predicates, one on the full view and one on the private"
          & " view",
         when Lim_Primitive_Call_In_DIC =>
           "a call to a primitive operation of a tagged type T occurring in "
          & "the default initial condition of T with the type instance as a "
          & "parameter",
         when Lim_Protected_Operation_Of_Component =>
           "a call to a protected operation of a protected component inside"
          & " a protected object",
         when Lim_Protected_Operation_Of_Formal =>
           "a call to a protected operation of the formal parameter of a"
          & " subprogram",
         when Lim_Refined_Post_On_Entry =>
           "a protected entry annotated with a Refined_Post",
         when Lim_Relaxed_Init_Access_Type =>
           "an access type used as a subcomponent of a type or"
          & " an object annotated with Relaxed_Initialization",
         when Lim_Relaxed_Init_Aliasing =>
            "an object annotated with Relaxed_Initialization"
          & " is part of an overlay",
         when Lim_Relaxed_Init_Concurrent_Type =>
           "a concurrent type used as a subcomponent of a type or"
          & " an object annotated with Relaxed_Initialization",
         when Lim_Relaxed_Init_Invariant =>
           "a type annotated with an invariant used as a subcomponent of a"
          & " type or an object annotated with Relaxed_Initialization",
         when Lim_Relaxed_Init_Part_Of_Variable =>
           "a variable annotated both with Relaxed_Initialization and as "
          & "Part_Of a concurrent object",
         when Lim_Relaxed_Init_Protected_Component =>
           "a protected component annotated with Relaxed_Initialization",
         when Lim_Relaxed_Init_Tagged_Type =>
           "a tagged type used as a subcomponent of a type or"
          & " an object annotated with Relaxed_Initialization",
         when Lim_Relaxed_Init_Variant_Part =>
            "a subtype with a discriminant constraint containing only"
          & " subcomponents whose type is annotated with"
          & " Relaxed_Initialization",
         when Lim_Subprogram_Before_Inv =>
           "a subprogram declaration occurring in a loop before the loop "
          & "invariant",
         when Lim_Suspension_On_Formal =>
           "a call to a suspend operation on a suspension formal parameter",
         when Lim_Target_Name_In_Borrow =>
           "an occurrence of the target name @ in an assignment to an object "
          & "of an anonymous access-to-variable type",
         when Lim_Target_Name_In_Move =>
           "an occurrence of the target name @ in an assignment to an object "
          & "containing subcomponents of a named access-to-variable type",
         when Lim_Type_Inv_Access_Type =>
           "an access type designating an incomplete or private type with a"
          & " subcomponent annotated with a type invariant",
         when Lim_Type_Inv_Nested_Package =>
           "a private type declared in a nested package annotated with a "
          & "type invariant",
         when Lim_Type_Inv_Private_Child =>
           "a private type declared in a private child package annotated with"
          & " a type invariant",
         when Lim_Type_Inv_Protected_Type =>
           "a protected type annotated with a type invariant",
         when Lim_Type_Inv_Tagged_Comp =>
           "a tagged type with a subcomponent annotated with a type invariant",
         when Lim_Type_Inv_Tagged_Type =>
           "a tagged type annotated with a type invariant",
         when Lim_Type_Inv_Volatile =>
           "a volatile object with asynchronous writers or readers and a type"
          & " invariant",
         when Lim_Uninit_Alloc_In_Expr_Fun =>
           "an uninitialized allocator inside an expression function",
         when Lim_Unknown_Alignment =>
           "a reference to the ""Alignment"" attribute on a prefix which is "
          & "not a type with an alignment clause",
         when Lim_UU_Tagged_Comp =>
           "a component of an unconstrained unchecked union type in a tagged "
          & "extension");

   pragma Annotate (Xcov, Exempt_Off);

   ---------------
   -- From_JSON --
   ---------------

   function From_JSON (V : JSON_Value) return Prover_Stat is
   begin
      return Prover_Stat'(Count     => Get (Get (V, "count")),
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
      Ar : constant JSON_Array :=
        (if Is_Empty (V)
         then Empty_Array
         else Get (V));

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

      Ar : constant JSON_Array := Get (V);
      Res : Cntexample_Lines :=
        Cntexample_Lines'(VC_Line        => Cntexample_Elt_Lists.Empty_List,
                          Other_Lines    => Cntexample_Line_Maps.Empty_Map,
                          Previous_Lines => Previous_Line_Maps.Empty_Map);

   begin
      for Var_Index in Positive range 1 .. Length (Ar) loop
         declare
            Elt : constant JSON_Value := Get (Ar, Var_Index);
            Loc : constant String := Get (Elt, "line");
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
        new Cntexmp_Value'(Get_Typed_Cntexmp_Value (
                           Get (Get (V, "value"), "value_concrete_term")));
   begin
      return
        Cntexample_Elt'(K           => Raw,
                        Kind        => From_JSON (Get (V, "kind")),
                        Name        => Get (Get (V, "name")),
                        Labels      =>
                          From_JSON_Labels (Get (Get (V, "attrs"))),
                        Value       => Cnt_Value);
   end From_JSON;

   function From_JSON (V : JSON_Value) return Cntexample_Elt_Lists.List is
      Res : Cntexample_Elt_Lists.List := Cntexample_Elt_Lists.Empty_List;
      Ar  : constant JSON_Array       :=
        (if Is_Empty (V)
         then Empty_Array
         else Get (V));
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
        (if S = "all" then All_In_SPARK
         elsif S = "spec" then Spec_Only_In_SPARK
         elsif S = "no" then Not_In_SPARK
         else raise Program_Error);
   end From_JSON;

   ----------------------
   -- From_JSON_Labels --
   ----------------------

   function From_JSON_Labels (Ar : JSON_Array) return S_String_List.List is
      Res : S_String_List.List  := S_String_List.Empty_List;
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

   -----------------------------
   -- Get_Typed_Cntexmp_Value --
   -----------------------------

   function Get_Typed_Cntexmp_Value (V : JSON_Value) return Cntexmp_Value is
      T : constant Cntexmp_Type := From_JSON (V);
   begin
      case T is
         when Cnt_Integer   =>
            return (T => Cnt_Integer,
                    I => Get (V, "val"));

         when Cnt_Decimal   =>
            return (T => Cnt_Decimal,
                    D => Get (V, "val"));

         --  Float values are complex so they are sent as JSON records. Example
         --  of values are infinities, zeroes, etc
         when Cnt_Float     =>
            declare
               Val        : constant JSON_Value := Get (V, "val");
               Float_Type : constant String := Get (Val, "float_type");
            begin
               if Float_Type = "Plus_infinity" then
                  return (T => Cnt_Float,
                          F =>
                             new Float_Value'(F_Type => Float_Plus_Infinity));

               elsif Float_Type = "Minus_infinity" then
                  return (T => Cnt_Float,
                          F =>
                             new Float_Value'(F_Type => Float_Minus_Infinity));

               elsif Float_Type = "Plus_zero" then
                  return (T => Cnt_Float,
                          F =>
                             new Float_Value'(F_Type => Float_Plus_Zero));

               elsif Float_Type = "Minus_zero" then
                  return (T => Cnt_Float,
                          F =>
                             new Float_Value'(F_Type => Float_Minus_Zero));

               elsif Float_Type = "Not_a_number" then
                  return (T => Cnt_Float,
                          F =>
                             new Float_Value'(F_Type => Float_NaN));

               elsif Float_Type = "Float_value" then
                  return (T => Cnt_Float,
                          F =>
                             new Float_Value'(F_Type        => Float_Val,
                                              F_Sign        =>
                                                Get (Val, "sign"),
                                              F_Exponent    =>
                                                Get (Val, "exp"),
                                              F_Significand =>
                                                Get (Val, "mant")));
               else
                  return (T => Cnt_Invalid,
                          S => Null_Unbounded_String);
               end if;
            end;

         when Cnt_Boolean   =>
            return (T  => Cnt_Boolean,
                    Bo => Get (V, "val"));

         when Cnt_Bitvector =>
            return (T => Cnt_Bitvector,
                    B => Get (Get (V, "val"), "bv_int"));

         when Cnt_Record    =>
            declare
               Record_Val : constant JSON_Array := Get (V, "val");
               Field_Value_List : Cntexmp_Value_Array.Map;

            begin

               for Index in 1 .. Length (Record_Val) loop
                  declare
                     Json_Element : constant JSON_Value :=
                         Get (Get (Record_Val, Index), "value");
                     Field_Name   : constant String :=
                         Get (Get (Record_Val, Index), "field");
                     Elem_Ptr     : constant Cntexmp_Value_Ptr :=
                       new Cntexmp_Value'(
                         Get_Typed_Cntexmp_Value (Json_Element));
                  begin
                     Field_Value_List.Insert (Field_Name, Elem_Ptr);
                  end;
               end loop;
               return (T  => Cnt_Record,
                       Fi => Field_Value_List);
            end;

         when Cnt_Projection =>
            --  All projections that gets to here should be removed. They are
            --  mostly to_reps.
            return
              Get_Typed_Cntexmp_Value (Get (Get (V, "val"), "proj_value"));

         when Cnt_Array     =>
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
                          new Cntexmp_Value'(Get_Typed_Cntexmp_Value
                                               (Get (Json_Element, "value")));
                     begin
                        case Indice_Type is
                        when Cnt_Integer | Cnt_Decimal | Cnt_Boolean =>
                           Cntexmp_Value_Array.Insert
                             (Indice_Array,
                              Get (Get (Json_Element, "indice"), "val"),
                              Elem_Ptr);

                        when Cnt_Bitvector =>
                           Cntexmp_Value_Array.Insert
                             (Indice_Array,
                              Get
                                (Get (Get (Json_Element, "indice"), "val"),
                                 "bv_int"),
                              Elem_Ptr);

                        when others =>
                           return (T => Cnt_Invalid,
                                   S => Null_Unbounded_String);
                        end case;
                     end;

                  end;
               end loop;
               Other_Ptr :=
                 new Cntexmp_Value'(Get_Typed_Cntexmp_Value (JS_Array_others));
               if Other_Ptr = null then
                  Other_Ptr :=
                    new Cntexmp_Value'(T => Cnt_Invalid,
                                       S => Null_Unbounded_String);

               end if;
               return (T             => Cnt_Array,
                       Array_Indices => Indice_Array,
                       Array_Others  => Other_Ptr);
            end;

         when Cnt_Invalid =>
            return (T => Cnt_Invalid,
                    S => Null_Unbounded_String);
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
             when VC_Division_Check => "divide by zero",
             when VC_Index_Check => "index check",
             when VC_Overflow_Check => "overflow check",
             when VC_FP_Overflow_Check => "fp_overflow check",
             when VC_Range_Check => "range check",
             when VC_Predicate_Check => "predicate check",
             when VC_Predicate_Check_On_Default_Value =>
               "predicate check on default value",
             when VC_Null_Pointer_Dereference => "null pointer dereference",
             when VC_Null_Exclusion => "null exclusion",
             when VC_Dynamic_Accessibility_Check =>
               "dynamic accessibility check",
             when VC_Resource_Leak => "resource or memory leak",
             when VC_Resource_Leak_At_End_Of_Scope =>
               "resource or memory leak at end of scope",
             when VC_Invariant_Check => "invariant check",
             when VC_Invariant_Check_On_Default_Value =>
               "invariant check on default value",
             when VC_Length_Check => "length check",
             when VC_Discriminant_Check => "discriminant check",
             when VC_Tag_Check => "tag check",
             when VC_Ceiling_Interrupt =>
               "ceiling priority in Interrupt_Priority",
             when VC_Interrupt_Reserved => "interrupt is reserved",
             when VC_Ceiling_Priority_Protocol => "ceiling priority protocol",
             when VC_Task_Termination => "task termination",
             when VC_Initial_Condition => "initial condition",
             when VC_Default_Initial_Condition => "default initial condition",
             when VC_Precondition => "precondition",
             when VC_Precondition_Main => "precondition of main",
             when VC_Postcondition => "postcondition",
             when VC_Refined_Post => "refined postcondition",
             when VC_Contract_Case => "contract case",
             when VC_Disjoint_Contract_Cases => "disjoint contract cases",
             when VC_Complete_Contract_Cases => "complete contract cases",
             when VC_Exceptional_Case => "exceptional case",
             when VC_Loop_Invariant => "loop invariant",
             when VC_Loop_Invariant_Init =>
               "loop invariant in first iteration",
             when VC_Loop_Invariant_Preserv =>
               "loop invariant after first iteration",
             when VC_Loop_Variant => "loop variant",
             when VC_Subprogram_Variant => "subprogram variant",
             when VC_Assert => "assertion",
             when VC_Assert_Premise => "assertion premise",
             when VC_Assert_Step => "assertion step",
             when VC_Raise => "raised exception",
             when VC_Feasible_Post => "feasible function",
             when VC_Inline_Check =>
               "Inline_For_Proof or Logical_Equal annotation",
             when VC_UC_Source => "unchecked conversion source check",
             when VC_UC_Target => "unchecked conversion target check",
             when VC_UC_Same_Size => "unchecked conversion size check",
             when VC_UC_Alignment => "alignment check",
             when VC_UC_Volatile => "volatile overlay check",
             when VC_Weaker_Pre =>
               "precondition weaker than class-wide precondition",
             when VC_Trivial_Weaker_Pre =>
               "precondition not True while class-wide precondition is True",
             when VC_Stronger_Post =>
               "postcondition stronger than class-wide postcondition",
             when VC_Weaker_Classwide_Pre =>
               "class-wide precondition weaker than overridden one",
             when VC_Stronger_Classwide_Post =>
               "class-wide postcondition stronger than overridden one",
             when VC_Weaker_Pre_Access =>
               "precondition of the source weaker than precondition of the"
               & " target",
             when VC_Stronger_Post_Access =>
               "postcondition of the source stronger than postcondition of the"
               & " target",
             when VC_Inconsistent_Pre =>
               "precondition always False",
             when VC_Inconsistent_Post =>
               "postcondition always False",
             when VC_Inconsistent_Assume =>
               "pragma Assume always False",
             when VC_Unreachable_Branch =>
               "unreachable branch",
             when VC_Dead_Code =>
               "unreachable code",
             when VC_Initialization_Check =>
               "use of an uninitialized variable",
             when VC_Unchecked_Union_Restriction =>
               "unchecked union restriction");
   end Kind_Name;

   function Kind_Name (Kind : Valid_Flow_Tag_Kind) return String is
     (case Kind is
         when Aliasing                                    =>
            "aliasing between subprogram parameters",
         when Call_In_Type_Invariant                      =>
            "invalid call in type invariant",
         when Call_To_Current_Task                        =>
            "invalid context for call to Current_Task",
         when Concurrent_Access                           =>
            "race condition",
         when Critical_Global_Missing                     =>
            "critically incomplete Global or Initializes contract",
         when Dead_Code                                   =>
            "dead code",
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
            "non-ghost output of ghost procedure",
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
            "illegal write of an object " &
            "declared as constant after elaboration",
         when Potentially_Blocking_In_Protected           =>
            "protected operation blocks",
         when Reference_To_Non_CAE_Variable               =>
            "illegal reference to a global object " &
            "in precondition of a protected operation",
         when Refined_State_Wrong                         =>
            "constant with no variable inputs " &
            "as an abstract state's constituent",
         when Side_Effects                                =>
            "function with side effects",
         when Stable                                      =>
            "loop with stable statement",
         when Subprogram_Termination                      =>
            "subprogram marked Terminating may not terminate",
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

   function Kind_Name (Kind : Misc_Warning_Kind) return String is
     (case Kind is
        when Warn_Address_To_Access =>
          "address to access conversion",
        when Warn_Alias_Atomic_Vol =>
          "volatile and atomic status of aliases",
        when Warn_Alias_Different_Volatility =>
          "volatile properties of aliases",
        when Warn_Attribute_Valid =>
          "attribute Valid always True",
        when Warn_Initialization_To_Alias =>
          "initialization of alias",
        when Warn_Function_Is_Valid =>
          "function Is_Valid always return True",
        when Warn_Pragma_Annotate_No_Check =>
          "no check message justified",
        when Warn_Pragma_Annotate_Proved_Check =>
          "proved check message justified",
        when Warn_Pragma_Annotate_Terminating =>
          "Terminating deprecated",
        when Warn_Pragma_External_Axiomatization =>
          "External Axiomatizations not supported",
        when Warn_Pragma_Ignored =>
          "pragma ignored",
        when Warn_Pragma_Overflow_Mode =>
          "Overflow_Mode ignored",
        when Warn_Precondition_Statically_False =>
          "precondition statically False",
        when Warn_Unreferenced_Function =>
          "unreferenced function",
        when Warn_Unreferenced_Procedure =>
          "unreferenced procedure",
        when Warn_Useless_Relaxed_Init_Fun =>
          "useless Relaxed_Initialization aspect on function result",
        when Warn_Useless_Relaxed_Init_Obj =>
          "useless Relaxed_Initialization aspect on object",
        when Warn_Useless_Always_Return_Fun =>
          "useless Always_Return annotation on function",
        when Warn_Useless_Always_Return_Lemma =>
          "useless Always_Return annotation on automatically instantiated"
           & " lemma",
        when Warn_Variant_Not_Recursive =>
          "variant not recursive",

        --  Warnings guaranteed to be issued
        when Warn_Address_Atomic =>
          "imprecise Address without Atomic",
        when Warn_Address_Valid =>
          "imprecise Address and validity",
        when Warn_Assumed_Volatile_Properties =>
          "imprecise Address and volatile properties",
        when Warn_Indirect_Writes_Through_Alias =>
          "imprecise Address and indirect writes through alias",
        when Warn_Indirect_Writes_To_Alias =>
          "imprecise Address and indirect writes to alias",
        when Warn_Assumed_Always_Return =>
          "assumed Always_Return",
        when Warn_Assumed_Global_Null =>
          "assumed Global null",

        --  Warnings only issued when using switch --pedantic
        when Warn_Image_Attribute_Length =>
          "string attribute length",
        when Warn_Operator_Reassociation =>
          "operator reassociation",
        when Warn_Representation_Attribute_Value =>
          "representation attribute value");

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
            when PC_Prover   => "prover",
            when PC_Trivial  => "trivial",
            when PC_Flow     => "flow");
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
      Obj : constant JSON_Value := Create_Object;
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
         Set_Field (Obj_Cur,
                    Line_Number_Image (Cntexample_Line_Maps.Key (C)),
                    To_JSON (L.Other_Lines (C)));
      end loop;
      for C in L.Previous_Lines.Iterate loop
         Set_Field (Obj_Prev,
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
        (Indices : Cntexmp_Value_Array.Map;
         Other   : Cntexmp_Value_Ptr)
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
      Set_Field (Obj, "name",  C.Name);
      Set_Field (Obj, "kind",  To_JSON (C.Kind));
      case C.K is
         when Raw =>
            Set_Field (Obj, "type", Cntexmp_Type'Image (C.Value.T));
            Set_Field (Obj, "full_value", To_JSON (C.Value.all));
         when Pretty_Printed =>
            Set_Field (Obj, "value", C.Val_Str.Str);
      end case;
      return Obj;
   end To_JSON;

   function To_JSON (L : Cntexample_Elt_Lists.List)
                     return JSON_Value
   is
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
            when All_In_SPARK => "all",
            when Spec_Only_In_SPARK => "spec",
            when Not_In_SPARK => "no");
   begin
      return Create (S);
   end To_JSON;

   ---------------
   -- To_String --
   ---------------

   function To_String (P : Prover_Category) return String is
   begin
      return (case P is
                 when PC_Prover   => "Automatic provers",
                 when PC_Trivial  => "Trivial",
                 when PC_Flow     => "Flow analysis");
   end To_String;

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
