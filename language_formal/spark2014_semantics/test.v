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
(* Procedure Body Declaration *)
      Sproc 3 (
        mkprocedure_body 4
          (* Procedure Body - Name *)
          (*Test_for_Coq*) 1
          (* Procedure Body - Specification *)
          (nil)
          (* Procedure Body - Parameters *)
          (nil) 
          (* Procedure Body - Locally Defined Variables *)
          (
          mklocal_declaration 5 (*N*) 1 1 (Some (Econst 6 (Ointconst 25))) :: 
          mklocal_declaration 7 (*Result*) 2 2 None :: 
          mklocal_declaration 8 (*I*) 3 1 None :: 
          mklocal_declaration 9 (*X*) 4 1 None :: nil)
          (* Procedure Body - Body *) (
            Sseq 10 (
              Sassign 11 ((*Result*) 2) (Econst 12 (Oboolconst true)) ) ( 
              Sseq 13 (
                Sifthen 14 (Ebinop 15 Cle (Evar 16 (*N*) 1) (Econst 17 (Ointconst 1))) (
                    Sassign 18 ((*Result*) 2) (Econst 19 (Oboolconst false))
                  ) ) ( 
                Sseq 20 (
                  Sassign 21 ((*I*) 3) (Econst 22 (Ointconst 2)) ) ( 
                  Swhile 23 (Ebinop 24 Cle (Ebinop 25 Omul (Evar 26 (*I*) 3) (Evar 27 (*I*) 3)) (Evar 28 (*N*) 1)) (
                      Sseq 29 (
                        Sassign 30 ((*X*) 4) (Ebinop 31 Odiv (Evar 32 (*N*) 1) (Evar 33 (*I*) 3)) ) ( 
                        Sseq 34 (
                          Sifthen 35 (Ebinop 36 Ceq (Evar 37 (*N*) 1) (Ebinop 38 Omul (Evar 39 (*X*) 4) (Evar 40 (*I*) 3))) (
                              Sassign 41 ((*Result*) 2) (Econst 42 (Oboolconst false))
                            ) ) ( 
                          Sassign 43 ((*I*) 3) (Ebinop 44 Oadd (Evar 45 (*I*) 3) (Econst 46 (Ointconst 1))) ) )
                    ) ) ) )
          )
      ).

Check f_prime.

Definition result := f_eval_subprogram 100 nil f_prime.

Eval compute in result.

Definition ast_num_inc := f_ast_num_inc_subprogram f_prime.

Eval compute in ast_num_inc.

Definition well_typed := f_well_typed_subprogram nil f_prime.

Eval compute in well_typed.

Definition well_initialized := f_well_defined_subprogram nil f_prime.

Eval compute in well_initialized.

Definition well_checked := f_check_generator_subprogram nil f_prime.

Eval compute in well_checked.

Definition run_time_checks := well_checked.

Definition result_with_checks := f_eval_subprogram_with_checks 100 run_time_checks nil f_prime.

Eval compute in result_with_checks.



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
     I := 0;
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
(* Procedure Body Declaration *)
      Sproc 3 (
        mkprocedure_body 4
          (* Procedure Body - Name *)
          (*Test_for_Coq1*) 1
          (* Procedure Body - Specification *)
          (nil)
          (* Procedure Body - Parameters *)
          (nil) 
          (* Procedure Body - Locally Defined Variables *)
          (
          mklocal_declaration 5 (*N*) 1 2 (Some (Econst 6 (Ointconst 25))) :: 
          mklocal_declaration 7 (*Result*) 2 3 None :: 
          mklocal_declaration 8 (*I*) 3 2 None :: 
          mklocal_declaration 9 (*X*) 4 2 None :: nil)
          (* Procedure Body - Body *) (
            Sseq 10 (
              Sassign 11 ((*Result*) 2) (Econst 12 (Oboolconst true)) ) ( 
              Sseq 13 (
                Sifthen 14 (Ebinop 15 Cle (Evar 16 (*N*) 1) (Econst 17 (Ointconst 1))) (
                    Sassign 18 ((*Result*) 2) (Econst 19 (Oboolconst false))
                  ) ) ( 
                Sseq 20 (
                  Sassign 21 ((*I*) 3) (Econst 22 (Ointconst 0)) ) ( 
                  Swhile 23 (Ebinop 24 Cle (Ebinop 25 Omul (Evar 26 (*I*) 3) (Evar 27 (*I*) 3)) (Evar 28 (*N*) 1)) (
                      Sseq 29 (
                        Sassign 30 ((*X*) 4) (Ebinop 31 Odiv (Evar 32 (*N*) 1) (Evar 33 (*I*) 3)) ) ( 
                        Sseq 34 (
                          Sifthen 35 (Ebinop 36 Ceq (Evar 37 (*N*) 1) (Ebinop 38 Omul (Evar 39 (*X*) 4) (Evar 40 (*I*) 3))) (
                              Sassign 41 ((*Result*) 2) (Econst 42 (Oboolconst false))
                            ) ) ( 
                          Sassign 43 ((*I*) 3) (Ebinop 44 Oadd (Evar 45 (*I*) 3) (Econst 46 (Ointconst 1))) ) )
                    ) ) ) )
          )
      ).

Definition result_1 := f_eval_subprogram 100 nil f_prime_div_zero.

Eval compute in result_1.

Definition run_time_checks_1 := f_check_generator_subprogram nil f_prime.

Eval compute in run_time_checks_1.

Definition result_with_checks_1 := f_eval_subprogram_with_checks 100 run_time_checks_1 nil f_prime_div_zero.

Eval compute in result_with_checks_1.

Definition result_without_checks_1 := f_eval_subprogram_with_checks 100 nil nil f_prime_div_zero.

Eval compute in result_without_checks_1.

Definition ast_num_inc_1 := f_ast_num_inc_subprogram f_prime_div_zero.

Eval compute in ast_num_inc_1.


(* ======================================================== *)
(* ======================================================== *)







