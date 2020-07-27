------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                              V C _ K I N D S                             --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2020, AdaCore                     --
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
   function To_JSON (L : Cntexample_Elt_Lists.List) return JSON_Value;
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

         when VC_Division_Check            => "369",

         --  CWE-120: Buffer Copy without Checking Size of Input ('Classic
         --  Buffer Overflow')

         when VC_Index_Check               => "120",

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

         --  CWE-401: Missing Release of Memory after Effective Lifetime

         when VC_Memory_Leak
            | VC_Memory_Leak_At_End_Of_Scope => "401",

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
            | VC_Contract_Case             => "682",

         --  CWE-843 Access of Resource Using Incompatible Type ('Type
         --  Confusion')

         when VC_UC_No_Holes
            | VC_UC_Same_Size              => "843",

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
            | VC_Complete_Contract_Cases
            | VC_Loop_Invariant
            | VC_Loop_Invariant_Init
            | VC_Loop_Invariant_Preserv
            | VC_Assert
            | VC_Raise
            | VC_Inline_Check
            | VC_Weaker_Pre
            | VC_Trivial_Weaker_Pre
            | VC_Stronger_Post
            | VC_Weaker_Classwide_Pre
            | VC_Stronger_Classwide_Post
            | VC_Weaker_Pre_Access
            | VC_Stronger_Post_Access
            | VC_Warning_Kind
            | VC_Null_Exclusion
            | VC_UC_Alignment
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

         when Unused
            | Unused_Initial_Value          => "563",

         --  CWE-1164: Irrelevant Code

         when Ineffective                   => "1164",

         --  CWE-674: Uncontrolled Recursion

         when Call_In_Type_Invariant
            | Subprogram_Termination        => "674",

         when Aliasing
            | Call_To_Current_Task
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
            | Pragma_Elaborate_All_Needed
            | Pragma_Elaborate_Body_Needed
            | Reference_To_Non_CAE_Variable
            | Refined_State_Wrong
            | Side_Effects
            | Stable
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
         when VC_Memory_Leak                      =>
            return "Check that the assignment does not lead to a memory leak";
         when VC_Memory_Leak_At_End_Of_Scope      =>
            return "Check that the declaration does not lead to a memory leak";
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
         when VC_Raise                            =>
            return "Check that the raise statement or expression can never " &
              "be reached.";
         when VC_Inline_Check                     =>
            return "Check that an Annotate pragma with the Inline_For_Proof " &
              "identifier is correct.";
         when VC_UC_No_Holes                      =>
            return "Check that a type in an unchecked conversion can safely " &
              "be used for such conversions. This means that the memory " &
              "occupied by objects of this type is fully used by the " &
              "object, and no invalid bitpatterns occur.";
         when VC_UC_Same_Size                     =>
            return "Check that the two types in an unchecked conversion " &
              "instance are of the same size.";
         when VC_UC_Alignment                     =>
            return "Check that the first object's alignment is an integral " &
              "multiple of the second object's alignment.";
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
         when Ghost_Wrong                                =>
            "A ghost procedure has a non-ghost global output.",
         when Global_Missing                              =>
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
         when Pragma_Elaborate_All_Needed                 =>
            "Use of an abstract state of a package " &
            "that was not yet elaborated.",
         when Pragma_Elaborate_Body_Needed                =>
            "A missing pragma Elaborate_Body.",
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
            "A loop with stable statement.",  --  ??? appears dead
         when Subprogram_Termination                      =>
            "A subprogram with Terminating annotation may not terminate.",
         when Uninitialized                               =>
            "Flow analysis has detected the use of an uninitialized variable.",
         when Unused                                      =>
            "A global or locally declared object is never used.",
         when Unused_Initial_Value                        =>
            "The initial value of an object is not used.",
         when Volatile_Function_Without_Volatile_Effects  =>
            "A non-volatile function wrongly declared as volatile.");

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

   function From_JSON (V : JSON_Value) return Prover_Category is
      S : constant String := Get (V);
   begin
      if S = "codepeer" then
         return PC_Codepeer;
      elsif S = "trivial" then
         return PC_Trivial;
      elsif S = "prover" then
         return PC_Prover;
      elsif S = "flow" then
         return PC_Flow;
      end if;
      raise Program_Error;
   end From_JSON;

   function From_JSON (V : JSON_Value) return CEE_Kind is
      S : constant String := Get (V);
   begin
      if S = "variable" then
         return CEE_Variable;
      elsif S = "error_message" then
         return CEE_Error_Msg;
      elsif S = "old" then
         return CEE_Old;
      elsif S = "result" then
         return CEE_Result;
      elsif S = "other" then
         return CEE_Other;
      end if;
      raise Program_Error;
   end From_JSON;

   function From_JSON (V : JSON_Value) return Cntexample_File_Maps.Map is

      Map : Cntexample_File_Maps.Map;

      procedure Process_Entry (Name : UTF8_String; Value : JSON_Value);

      -------------------
      -- Process_Entry --
      -------------------

      procedure Process_Entry (Name : UTF8_String; Value : JSON_Value) is
      begin
         Map.Insert (Name, From_JSON (Value));
      end Process_Entry;

   --  Start of processing for From_JSON

   begin
      Map_JSON_Object (V, Process_Entry'Access);
      return Map;
   end From_JSON;

   function From_JSON (V : JSON_Value) return Cntexample_Lines is
      Res : Cntexample_Lines :=
        Cntexample_Lines'(VC_Line        =>
                            (if Has_Field (V, "vc_line")
                             then From_JSON ((Get (V, "vc_line")))
                             else Cntexample_Elt_Lists.Empty_List),
                          Other_Lines    => Cntexample_Line_Maps.Empty_Map,
                          Previous_Lines => Previous_Line_Maps.Empty_Map);

      procedure Process_Entry (Name : UTF8_String; Value : JSON_Value);

      -------------------
      -- Process_Entry --
      -------------------

      procedure Process_Entry (Name : UTF8_String; Value : JSON_Value) is
      begin
         if Name /= "vc_line" then
            Res.Other_Lines.Insert
              (Natural'Value (Name), From_JSON (Value));
         end if;
      end Process_Entry;

   --  Start of processing for From_JSON

   begin
      Map_JSON_Object (V, Process_Entry'Access);
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

      if E = "Decimal" then
         return Cnt_Decimal;
      end if;

      if E = "Float" then
         return Cnt_Float;
      end if;

      if E = "Boolean" then
         return Cnt_Boolean;
      end if;

      if E = "Bv" then
         return Cnt_Bitvector;
      end if;

      if E = "Unparsed" then
         return Cnt_Unparsed;
      end if;

      if E = "Array" then
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
        new Cntexmp_Value'(Get_Typed_Cntexmp_Value (Get (V, "value")));
   begin
      return
        Cntexample_Elt'(Kind        => From_JSON (Get (V, "kind")),
                        Name        => Get (Get (V, "name")),
                        Labels      =>
                          From_JSON_Labels (Get (Get (V, "attrs"))),
                        Value       => Cnt_Value,
                        Val_Str     => (Nul => False,
                                        Str => Null_Unbounded_String));
   end From_JSON;

   function From_JSON (V : JSON_Value) return Cntexample_Elt_Lists.List is
      Res : Cntexample_Elt_Lists.List := Cntexample_Elt_Lists.Empty_List;
      Ar  : constant JSON_Array       := Get (V);
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
               Float_Type : constant String := Get (Val, "cons");
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
                                                Get (Val, "exponent"),
                                              F_Significand =>
                                                Get (Val, "significand")));
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
                    B => Get (V, "val"));

         when Cnt_Unparsed  =>
            return (T => Cnt_Unparsed,
                    U => Get (V, "val"));

         when Cnt_Record    =>
            declare
               Record_Val : constant JSON_Value := Get (V, "val");
               Field_Value_List : Cntexmp_Value_Array.Map;
               JS_Array_Field   : constant JSON_Array :=
                                    Get (Record_Val, "Field");

            begin

               for Index in 1 .. Length (JS_Array_Field) loop
                  declare
                     Json_Element : constant JSON_Value :=
                         Get (Get (JS_Array_Field, Index), "value");
                     Field_Name   : constant String :=
                         Get (Get (JS_Array_Field, Index), "field");
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
            return Get_Typed_Cntexmp_Value (Get (V, "value"));

         when Cnt_Array     =>
            declare
               JS_Array     : constant JSON_Array := Get (V, "val");
               Indice_Array : Cntexmp_Value_Array.Map;
               Other_Ptr    : Cntexmp_Value_Ptr := null;

            begin
               for Index in 1 .. Length (JS_Array) loop
                  declare
                     Json_Element : constant JSON_Value :=
                       Get (JS_Array, Index);

                  begin
                     if Has_Field (Json_Element, "others") then
                        declare
                           V : constant JSON_Value :=
                             Get (Json_Element, "others");
                        begin
                           pragma Assert (Other_Ptr = null);
                           Other_Ptr := new Cntexmp_Value'(
                                              Get_Typed_Cntexmp_Value (V));
                        end;
                     else
                        declare
                           --  Indices are sent by Why3 as JSON model_value.
                           --  This is only accepted here if the model_value
                           --  is actually a simple value: integer, boolean...
                           --  And, on SPARK input, non simple value cannot
                           --  be produced.
                           Indice   : constant String :=
                              Get (Get (Json_Element, "indice"), "val");
                           Elem_Ptr : constant Cntexmp_Value_Ptr :=
                                        new Cntexmp_Value'(
                                          Get_Typed_Cntexmp_Value
                                            (Get (Json_Element, "value")));
                        begin
                           Cntexmp_Value_Array.Insert
                             (Indice_Array, Indice, Elem_Ptr);
                        end;
                     end if;

                  end;
               end loop;
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
             when VC_Memory_Leak => "memory leak",
             when VC_Memory_Leak_At_End_Of_Scope =>
               "memory leak at end of scope",
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
             when VC_Loop_Invariant => "loop invariant",
             when VC_Loop_Invariant_Init =>
               "loop invariant in first iteration",
             when VC_Loop_Invariant_Preserv =>
               "loop invariant after first iteration",
             when VC_Loop_Variant => "loop variant",
             when VC_Assert => "assertion",
             when VC_Raise => "raised exception",
             when VC_Inline_Check => "Inline_For_Proof annotation",
             when VC_UC_No_Holes => "unchecked conversion check",
             when VC_UC_Same_Size => "unchecked conversion size check",
             when VC_UC_Alignment => "alignment check",
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
               "use of an uninitialized variable");
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
         when Ghost_Wrong                                =>
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
         when Pragma_Elaborate_All_Needed                 =>
            "use of an abstract state of a package " &
            "that was not yet elaborated",
         when Pragma_Elaborate_Body_Needed                =>
            "a missing pragma Elaborate_Body",
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
            "loop with stable statement",  --  ??? appears dead
         when Subprogram_Termination                      =>
            "subprogram marked Terminating may not terminate",
         when Uninitialized                               =>
            "use of an uninitialized variable",
         when Unused                                      =>
            "object is not used",
         when Unused_Initial_Value                        =>
            "initial value of an object is not used",
         when Volatile_Function_Without_Volatile_Effects  =>
            "non-volatile function wrongly declared as volatile");

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
            when PC_Codepeer => "codepeer",
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

   function To_JSON (C : Cntexample_Elt) return JSON_Value is
      Obj : constant JSON_Value := Create_Object;
   begin
      Set_Field (Obj, "name",  C.Name);
      Set_Field (Obj, "value", C.Val_Str.Str);
      Set_Field (Obj, "kind",  To_JSON (C.Kind));
      return Obj;
   end To_JSON;

   function To_JSON (L : Cntexample_Elt_Lists.List)
                     return JSON_Value is
      Result : JSON_Array := Empty_Array;
   begin
      for Elt of L loop
         Append (Result, To_JSON (Elt));
      end loop;
      return Create (Result);
   end To_JSON;

   ---------------
   -- To_String --
   ---------------

   function To_String (P : Prover_Category) return String is
   begin
      return (case P is
                 when PC_Prover   => "Automatic provers",
                 when PC_Trivial  => "Trivial",
                 when PC_Codepeer => "CodePeer",
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
