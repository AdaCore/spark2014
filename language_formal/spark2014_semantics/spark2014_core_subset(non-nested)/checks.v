Require Export language.

(** * Run-Time Checks *)
(** a subset of run time checks to be verified *)
(**
     - Division Check
       
       Check that the second operand of the the division, mod or rem 
       operation is different from zero.

     - Overflow Check

       Check that the result of the given arithmetic operation is within 
       the bounds of the base type.

     - Range Check
       
       Check that the given value is within the bounds of the expected scalar 
       subtype.

     - Do_Range_Check_On_CopyOut
      
       for a procedure call, if it's required a range check for its input variables
       during copy_in procedure, then the range check flag should be set for its input
       arguments; but if it's required a range check for its output variables during
       copy_out procedure, then the range check flag should be set for its output 
       parameters instead of its output arguments, but it's unreasonable to set the
       range check on formal parameters of the called procedure as it maybe called in
       different context where there are no range check requirement. So here we introduce
       a new check flag Do_Range_Check_On_CopyOut for the output parameters but it's set
       on the output arguments.
 
     - Undefined_Check
     
       for any run time checks extracted from gnat2xml other than Do_Division_Check, 
       Do_Overflow_Check and Do_Range_Check, they are represented by Undefined_Check.
*)

(** 
      Do_Range_Check (Flag9-Sem) (reference: sinfo.ads)
 
         This flag is set on an expression which appears in a context where a
         range check is required. The target type is clear from the context.
         The contexts in which this flag can appear are the following:

   -     Right side of an assignment. In this case the target type is
         taken from the left side of the assignment, which is referenced
         by the Name of the N_Assignment_Statement node.

   -     Subscript expressions in an indexed component. In this case the
         target type is determined from the type of the array, which is
         referenced by the Prefix of the N_Indexed_Component node.

   -     Argument expression for a parameter, appearing either directly in
         the Parameter_Associations list of a call or as the Expression of an
         N_Parameter_Association node that appears in this list. In either
         case, the check is against the type of the formal. Note that the
         flag is relevant only in IN and IN OUT parameters, and will be
         ignored for OUT parameters, where no check is required in the call,
         and if a check is required on the return, it is generated explicitly
         with a type conversion.

   -     Initialization expression for the initial value in an object
         declaration. In this case the Do_Range_Check flag is set on
         the initialization expression, and the check is against the
         range of the type of the object being declared. This includes the
         cases of expressions providing default discriminant values, and
         expressions used to initialize record components.

   -     The expression of a type conversion. In this case the range check is
         against the target type of the conversion. See also the use of
         Do_Overflow_Check on a type conversion. The distinction is that the
         overflow check protects against a value that is outside the range of
         the target base type, whereas a range check checks that the
         resulting value (which is a value of the base type of the target
         type), satisfies the range constraint of the target type.
*)


(** checks that are needed to be verified at run time: *)

Inductive check_flag: Type := 
    | Do_Division_Check         : check_flag
    | Do_Overflow_Check         : check_flag
    | Do_Range_Check            : check_flag
    | Do_Range_Check_On_CopyOut : check_flag
    | Undefined_Check           : check_flag.


(** For an expression or statement, there may exists a list of checks 
    enforced on it, for example, for division expression, both
    division by zero and overflow checks are needed to be performed;
*)
Definition check_flags := list check_flag.

(** * Check Flags Comparison Functions *)

Function beq_check_flag (ck1 ck2: check_flag): bool :=
  match ck1, ck2 with
  | Do_Division_Check, Do_Division_Check => true
  | Do_Overflow_Check, Do_Overflow_Check => true
  | Do_Range_Check,    Do_Range_Check    => true
  | Do_Range_Check_On_CopyOut, Do_Range_Check_On_CopyOut => true
  | Undefined_Check, Undefined_Check => true
  | _, _ => false
  end.

Function element_of (a: check_flag) (ls: list check_flag): bool :=
  match ls with
  | nil => false
  | (a' :: ls') => 
      if beq_check_flag a a' then
        true
      else
        element_of a ls'
  end.

Function subset_of (cks1 cks2: check_flags): bool :=
  match cks1 with
  | nil => true
  | ck :: cks1' => 
      if element_of ck cks2 then
        subset_of cks1' cks2 
      else
        false
  end.

Function beq_check_flags (cks1 cks2: check_flags): bool :=
  (subset_of cks1 cks2) && (subset_of cks2 cks1).
