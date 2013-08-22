Require Import semantics.
Require Import wellformedness.

(****************
  - Example 1 -
 ****************)

(* = = = = = = = = = = = = = =
  procedure Test_for_Coq
  is 
     N: Integer := 25;
     Result: Boolean;
     I: Integer;
     X: Integer;
  begin
     Result := true;
     if N <= 1 then
        Result := false;
     end if;
     I := 2;
     while I*I <= N loop
        X := N / I;
        if N = X * I then
           Result := false;
        end if;
        I := I + 1;
     end loop;
  end Test_for_Coq;
 = = = = = = = = = = = = = =*)

Definition f_prime :=
Procedure 3 (
        mkprocedure_body 4
          (* Procedure Body - Name *)
          (*Test_for_Coq*) 1
          (* Procedure Body - Specification *)
          (nil)
          (* Procedure Body - Parameters *)
          (nil) 
          (* Procedure Body - Variable Declarations *)
          (
          mkobject_declaration 5 (*N*) 1 1 (Some (E_Literal 6 (Integer_Literal 25))) :: 
          mkobject_declaration 7 (*Result*) 2 2 None :: 
          mkobject_declaration 8 (*I*) 3 1 None :: 
          mkobject_declaration 9 (*X*) 4 1 None :: nil)
          (* Procedure Body - Statements *) (
            S_Sequence 10 (
              S_Assignment 11 ((*Result*) 2) (E_Literal 12 (Boolean_Literal true)) ) ( 
              S_Sequence 13 (
                S_If 14 (E_Binary_Operation 15 Less_Than_Or_Equal (E_Identifier 16 (*N*) 1) (E_Literal 17 (Integer_Literal 1))) (
                    S_Assignment 18 ((*Result*) 2) (E_Literal 19 (Boolean_Literal false))
                  ) ) ( 
                S_Sequence 20 (
                  S_Assignment 21 ((*I*) 3) (E_Literal 22 (Integer_Literal 2)) ) ( 
                  S_While_Loop 23 (E_Binary_Operation 24 Less_Than_Or_Equal (E_Binary_Operation 25 Multiply (E_Identifier 26 (*I*) 3) (E_Identifier 27 (*I*) 3)) (E_Identifier 28 (*N*) 1)) (
                      S_Sequence 29 (
                        S_Assignment 30 ((*X*) 4) (E_Binary_Operation 31 Divide (E_Identifier 32 (*N*) 1) (E_Identifier 33 (*I*) 3)) ) ( 
                        S_Sequence 34 (
                          S_If 35 (E_Binary_Operation 36 Equal (E_Identifier 37 (*N*) 1) (E_Binary_Operation 38 Multiply (E_Identifier 39 (*X*) 4) (E_Identifier 40 (*I*) 3))) (
                              S_Assignment 41 ((*Result*) 2) (E_Literal 42 (Boolean_Literal false))
                            ) ) ( 
                          S_Assignment 43 ((*I*) 3) (E_Binary_Operation 44 Plus (E_Identifier 45 (*I*) 3) (E_Literal 46 (Integer_Literal 1))) ) )
                    ) ) ) )
          )).

(* 1. program is syntax correct *)
Check f_prime.

(* 2. run the program in reference semantics *)
Definition result := f_eval_subprogram 100 nil f_prime.

Eval compute in result.

(* 3. program with right checks at right places should be semantical equivelent with reference semantics  *)

Definition expected_run_time_checks := f_check_generator_subprogram nil f_prime.

Eval compute in expected_run_time_checks.

Definition result_with_checks := f_eval_subprogram_with_checks 100 expected_run_time_checks nil f_prime.

Eval compute in result_with_checks.

(* 4. certified static analyzer *)

Definition ast_num_inc := f_ast_num_inc_subprogram f_prime.

Eval compute in ast_num_inc.

(* 4.1 well-typed *)
Definition well_typed := f_well_typed_subprogram nil f_prime.

Eval compute in well_typed.

(* 4.2 well-defined *)
Definition well_initialized := f_well_defined_subprogram nil f_prime.

Eval compute in well_initialized.

(* 4.3 well-checked *)
Definition actual_run_time_checks := expected_run_time_checks.

Definition well_checked := f_checks_match actual_run_time_checks expected_run_time_checks.

Eval compute in well_checked.

(* 4.4 well-formed (well-typed, well-defined and well-checked) program should always run correctly *)
Definition result_with_checks' := f_eval_subprogram_with_checks 100 actual_run_time_checks nil f_prime.

Eval compute in result_with_checks'.


(****************
  - Example 2 -
 ****************)

(* = = = = = = = = = = = = = =
  procedure Test_for_Coq1
  is 
     N: Integer := 25;
     Result: Boolean;
     I: Integer;
     X: Integer;
  begin
     Result := true;
     if N <= 1 then
        Result := false;
     end if;
     I := 0; (** coding error ! **)
     while I*I <= N loop
        X := N / I;
        if N = X * I then
           Result := false;
        end if;
        I := I + 1;
     end loop;
  end Test_for_Coq1;
 = = = = = = = = = = = = = =*)

Definition f_prime_div_zero :=
Procedure 3 (
        mkprocedure_body 4
          (* Procedure Body - Name *)
          (*Test_for_Coq1*) 1
          (* Procedure Body - Specification *)
          (nil)
          (* Procedure Body - Parameters *)
          (nil) 
          (* Procedure Body - Variable Declarations *)
          (
          mkobject_declaration 5 (*N*) 1 1 (Some (E_Literal 6 (Integer_Literal 25))) :: 
          mkobject_declaration 7 (*Result*) 2 2 None :: 
          mkobject_declaration 8 (*I*) 3 1 None :: 
          mkobject_declaration 9 (*X*) 4 1 None :: nil)
          (* Procedure Body - Statements *) (
            S_Sequence 10 (
              S_Assignment 11 ((*Result*) 2) (E_Literal 12 (Boolean_Literal true)) ) ( 
              S_Sequence 13 (
                S_If 14 (E_Binary_Operation 15 Less_Than_Or_Equal (E_Identifier 16 (*N*) 1) (E_Literal 17 (Integer_Literal 1))) (
                    S_Assignment 18 ((*Result*) 2) (E_Literal 19 (Boolean_Literal false))
                  ) ) ( 
                S_Sequence 20 (
                  S_Assignment 21 ((*I*) 3) (E_Literal 22 (Integer_Literal 0)) ) ( 
                  S_While_Loop 23 (E_Binary_Operation 24 Less_Than_Or_Equal (E_Binary_Operation 25 Multiply (E_Identifier 26 (*I*) 3) (E_Identifier 27 (*I*) 3)) (E_Identifier 28 (*N*) 1)) (
                      S_Sequence 29 (
                        S_Assignment 30 ((*X*) 4) (E_Binary_Operation 31 Divide (E_Identifier 32 (*N*) 1) (E_Identifier 33 (*I*) 3)) ) ( 
                        S_Sequence 34 (
                          S_If 35 (E_Binary_Operation 36 Equal (E_Identifier 37 (*N*) 1) (E_Binary_Operation 38 Multiply (E_Identifier 39 (*X*) 4) (E_Identifier 40 (*I*) 3))) (
                              S_Assignment 41 ((*Result*) 2) (E_Literal 42 (Boolean_Literal false))
                            ) ) ( 
                          S_Assignment 43 ((*I*) 3) (E_Binary_Operation 44 Plus (E_Identifier 45 (*I*) 3) (E_Literal 46 (Integer_Literal 1))) ) )
                    ) ) ) )
          )
      ).

(* 1. run the program in reference semantics *)
Definition result_1 := f_eval_subprogram 100 nil f_prime_div_zero.

Eval compute in result_1.

(* 2.1 well-typed *)
Definition well_typed_1 := f_well_typed_subprogram nil f_prime_div_zero.

Eval compute in well_typed_1.

(* 2.2 well-defined *)
Definition well_initialized_1 := f_well_defined_subprogram nil f_prime_div_zero.

Eval compute in well_initialized_1.

(* 2.3 well-checked *)
Definition expected_run_time_checks_1 := f_check_generator_subprogram nil f_prime_div_zero.

Eval compute in expected_run_time_checks_1.

Definition actual_run_time_checks_1 := expected_run_time_checks_1.

Definition well_checked_1 := f_checks_match actual_run_time_checks_1 expected_run_time_checks_1.

Eval compute in well_checked_1.

(* 2.4 well-formed (well-typed, well-defined and well-checked) program should always run correctly *)
Definition result_with_checks_1 := f_eval_subprogram_with_checks 100 actual_run_time_checks_1 nil f_prime_div_zero.

Eval compute in result_with_checks_1.


(* 3 not well-checked *)
Definition not_complete_checks := (44, Do_Overflow_Check :: nil)
       :: (38, Do_Overflow_Check :: nil)
          :: (31, Do_Overflow_Check :: nil)
             :: (25, Do_Overflow_Check :: nil) :: nil.

Definition result_with_bad_checks := f_eval_subprogram_with_checks 100 not_complete_checks nil f_prime_div_zero.

Eval compute in result_with_bad_checks.

(* ast numbers are unique *)
Definition ast_num_inc_1 := f_ast_num_inc_subprogram f_prime_div_zero.

Eval compute in ast_num_inc_1.

(****************
  - Example 3 -
 ****************)

(* = = = = = = = = = = = = = =
  procedure Uninitialized
  is 
     N: Integer;  (** N should be initialized before its usage ! **)
     Result: Boolean;
     I: Integer;
     X: Integer;
  begin
     Result := true;
     if N <= 1 then
        Result := false;
     end if;
     I := 0; (** coding error ! **)
     while I*I <= N loop
        X := N / I;
        if N = X * I then
           Result := false;
        end if;
        I := I + 1;
     end loop;
  end Test_for_Coq1;
 = = = = = = = = = = = = = =*)

Definition f_prime_uninitialized :=
(* Procedure Body Declaration *)
      Procedure 3 (
        mkprocedure_body 4
          (* Procedure Body - Name *)
          (*Uninitialized*) 1
          (* Procedure Body - Specification *)
          (nil)
          (* Procedure Body - Parameters *)
          (nil) 
          (* Procedure Body - Variable Declarations *)
          (
          mkobject_declaration 5 (*N*) 1 1 None :: 
          mkobject_declaration 6 (*Result*) 2 2 None :: 
          mkobject_declaration 7 (*I*) 3 1 None :: 
          mkobject_declaration 8 (*X*) 4 1 None :: nil)
          (* Procedure Body - Statements *) (
            S_Sequence 9 (
              S_Assignment 10 ((*Result*) 2) (E_Literal 11 (Boolean_Literal true)) ) ( 
              S_Sequence 12 (
                S_If 13 (E_Binary_Operation 14 Less_Than_Or_Equal (E_Identifier 15 (*N*) 1) (E_Literal 16 (Integer_Literal 1))) (
                    S_Assignment 17 ((*Result*) 2) (E_Literal 18 (Boolean_Literal false))
                  ) ) ( 
                S_Sequence 19 (
                  S_Assignment 20 ((*I*) 3) (E_Literal 21 (Integer_Literal 2)) ) ( 
                  S_While_Loop 22 (E_Binary_Operation 23 Less_Than_Or_Equal (E_Binary_Operation 24 Multiply (E_Identifier 25 (*I*) 3) (E_Identifier 26 (*I*) 3)) (E_Identifier 27 (*N*) 1)) (
                      S_Sequence 28 (
                        S_Assignment 29 ((*X*) 4) (E_Binary_Operation 30 Divide (E_Identifier 31 (*N*) 1) (E_Identifier 32 (*I*) 3)) ) ( 
                        S_Sequence 33 (
                          S_If 34 (E_Binary_Operation 35 Equal (E_Identifier 36 (*N*) 1) (E_Binary_Operation 37 Multiply (E_Identifier 38 (*X*) 4) (E_Identifier 39 (*I*) 3))) (
                              S_Assignment 40 ((*Result*) 2) (E_Literal 41 (Boolean_Literal false))
                            ) ) ( 
                          S_Assignment 42 ((*I*) 3) (E_Binary_Operation 43 Plus (E_Identifier 44 (*I*) 3) (E_Literal 45 (Integer_Literal 1))) ) )
                    ) ) ) )
          )
      ).

(* 1 well-typed *)
Definition well_typed_2 := f_well_typed_subprogram nil f_prime_uninitialized.

Eval compute in well_typed.

(* 2 well-defined *)
Definition well_initialized_2 := f_well_defined_subprogram nil f_prime_uninitialized.

Eval compute in well_initialized_2.

(* 3 well-checked *)
Definition expected_run_time_checks_2 := f_check_generator_subprogram nil f_prime_uninitialized.

Eval compute in expected_run_time_checks_2.

Definition result_with_checks_2 := f_eval_subprogram_with_checks 100 expected_run_time_checks_2 nil f_prime_uninitialized.

Eval compute in result_with_checks_2.

(* 4. run the program in reference semantics *)
Definition result_2 := f_eval_subprogram 100 nil f_prime_uninitialized.

Eval compute in result_2.



(* ======================================================== *)
(* ======================================================== *)






