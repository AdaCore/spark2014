Require Export semantics_flagged.
Require Export X_SparkTactics.


Scheme expression_ind := Induction for expression Sort Prop 
                         with name_ind := Induction for name Sort Prop.

Check expression_ind.

Lemma gen_check_flags_on_binop_completeness: forall op v1 v2 v3 ast_num e1 e2 checkflags v3',
  do_run_time_check_on_binop op v1 v2 v3 ->
    gen_check_flags (E_Binary_Operation ast_num op e1 e2) checkflags ->
      do_flagged_checks_on_binop checkflags op v1 v2 v3' ->
        v3 = v3'.
Proof.
  intros;
  destruct op; inversion H0; smack;
  repeat progress match goal with
    | [H: do_run_time_check_on_binop _ _ _ _, H1: do_flagged_checks_on_binop nil _ _ _ _ |- _] => inversion H; inversion H1; clear H H1; smack
    | [H: do_flagged_checks_on_binop _ _ _ _ _ |- _] => inversion H; clear H; smack
    | [H: do_flagged_check_on_binop _ _ _ _ _ |- _] => inversion H; clear H; smack 
    | [H: do_run_time_check_on_binop _ _ _ _ |- _] => inversion H; clear H; smack
    | [H1: do_overflow_check _ _ _ _, H2: do_overflow_check _ _ _ _ |- _] => inversion H1; inversion H2; smack
    | [H1: do_division_check _ _ _ _, H2: do_division_check _ _ _ _ |- _] => inversion H1; inversion H2; smack
    end.
Qed.

Lemma gen_check_flags_on_unop_completeness: forall op v v' ast_num e checkflags v'',
  do_run_time_check_on_unop op v v' ->
    gen_check_flags (E_Unary_Operation ast_num op e) checkflags ->
      do_flagged_checks_on_unop checkflags op v v'' ->
        v' = v''.
Proof.
  intros;
  destruct op; inversion H0; clear H0; smack;
  repeat progress match goal with
    | [H: do_flagged_checks_on_unop _ _ _ _ |- _] => inversion H; clear H; smack
    | [H: do_flagged_check_on_unop _ _ _ _ |- _] => inversion H; clear H; smack  
    | [H : do_run_time_check_on_unop _ _ _ |- _] => inversion H; clear H; smack
    | [H1: do_overflow_check_on_unop _ _ _, H2: do_overflow_check_on_unop _ _ _ |- _] => inversion H1; inversion H2; smack
    end.
Qed.

Lemma gen_index_check_flags_completeness: forall i l u v ast_num x_ast_num x e checkflags v',
  do_index_check i l u v ->
  gen_name_check_flags (E_Indexed_Component ast_num x_ast_num x e) checkflags ->
  do_flagged_index_checks checkflags i l u v' ->
  v = v'.
Proof.
  intros;
  repeat progress match goal with
    | [H: gen_name_check_flags _ _ |- _] => inversion H; clear H; smack 
    | [H: do_flagged_index_checks _ _ _ _ _ |- _] => inversion H; clear H; smack
    | [H: do_flagged_index_check _ _ _ _ _ |- _] => inversion H; clear H; smack  
    | [H1: do_index_check _ _ _ _, H2: do_index_check _ _ _ _ |- _] => inversion H1; inversion H2; smack
    end.
Qed.


Lemma expression_checks_completeness: forall e e' s v v',
  eval_expr s e v ->
    eval_expr_x s e' v' ->
      compile2_flagged_exp e e' ->
        v = v'.
Proof.
  apply (expression_ind
    (fun e: expression => forall (e' : expression_x) (s : STACK.stack) (v v' : Return value),
      eval_expr s e v ->
      eval_expr_x s e' v' ->
      compile2_flagged_exp e e' ->
      v = v')
    (fun e: name => forall (e': name_x) (s : STACK.stack) (v v' : Return value),
      eval_name s e v ->
      eval_name_x s e' v' ->
      compile2_flagged_name e e' ->
      v = v')
    ); smack;
  match goal with
  | [H: compile2_flagged_exp _ _ |- _] => inversion H; clear H; smack
  | [H: compile2_flagged_name _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H1: eval_expr _ _ _, H2: eval_expr_x _ _ _ |- _] => inversion H1; inversion H2; clear H1 H2; smack
  | [H1: eval_name _ _ _, H2: eval_name_x _ _ _ |- _] => inversion H1; inversion H2; clear H1 H2; smack
  end;
  repeat progress match goal with
    | [H1: compile2_flagged_exp ?e ?e_flagged, H2: eval_expr _ ?e _, H3: eval_expr_x _ ?e_flagged _ |- _] => 
        try ((specialize (H _ _ _ _ H2 H3 H1) || specialize (H0 _ _ _ _ H2 H3 H1)); clear H1 H2 H3; smack) 
    | [H1: Normal ?v1 = Normal ?v2 |- _] => inversion H; clear H; smack
    | [H1: STACK.fetchG ?i ?s = ?v1, H2: STACK.fetchG ?i ?s = ?v2 |- _ ] => rewrite H1 in H2; clear H1; smack 
  end;
  match goal with 
  | [H1: gen_check_flags (E_Binary_Operation _ ?op ?e1 ?e2) ?checkflags, 
     H2: do_flagged_checks_on_binop ?checkflags ?op ?v1 ?v2 _,
     H3: do_run_time_check_on_binop ?op ?v1 ?v2 _ |- _] => 
      specialize (gen_check_flags_on_binop_completeness _ _ _ _ _ _ _ _ _ H3 H1 H2); smack
  | [H1: gen_check_flags (E_Unary_Operation _ ?op ?e) ?checkflags, 
     H2: do_flagged_checks_on_unop ?checkflags ?op ?v _,
     H3: do_run_time_check_on_unop ?op ?v _ |- _] => 
      specialize (gen_check_flags_on_unop_completeness _ _ _ _ _ _ _ H3 H1 H2); smack
  | [H1: gen_name_check_flags ?e ?checkflags, 
     H2: do_flagged_index_checks ?checkflags ?i ?l ?u _,
     H3: do_index_check ?i ?l ?u _ |- _] =>
       specialize (gen_index_check_flags_completeness _ _ _ _ _ _ _ _ _ _ H3 H1 H2); smack
   | _ => idtac
  end.
Qed.

(*
Lemma expression_checks_completeness: forall e e' s v v',
  eval_expr s e v ->
    eval_expr_x s e' v' ->
      compile2_flagged_exp e e' ->
        v = v'.
Proof.
  apply (expression_ind
    (fun e: expression => forall (e' : expression_x) (s : STACK.stack) (v v' : Return value),
      eval_expr s e v ->
      eval_expr_x s e' v' ->
      compile2_flagged_exp e e' ->
      v = v')
    (fun e: name => forall (e': name_x) (s : STACK.stack) (v v' : Return value),
      eval_name s e v ->
      eval_name_x s e' v' ->
      compile2_flagged_name e e' ->
      v = v')
    ); smack.
- repeat progress match goal with
    | [H: compile2_flagged_exp _ _ |- _] =>  inversion H; clear H; smack
    | [H1: eval_expr _ _ _, H2: eval_expr_x _ _ _ |- _] => inversion H1; inversion H2; smack
    end.
- repeat progress match goal with
    | [H: compile2_flagged_exp _ _ |- _] => inversion H; clear H; smack
    | [H1 : eval_expr _ _ _, H2: eval_expr_x _ _ _ |- _] => inversion H1; inversion H2; smack
    end.
- match goal with
  | [H: compile2_flagged_exp _ _ |- _] => inversion H; clear H; smack
  end.
  match goal with
  | [H1: eval_expr _ _ _, H2: eval_expr_x _ _ _ |- _] => inversion H1; inversion H2; clear H1 H2; subst
  end;
  repeat progress match goal with
  | [H1: compile2_flagged_exp ?e ?e_flagged, H2: eval_expr _ ?e _, H3: eval_expr_x _ ?e_flagged _ |- _] => 
      try ((specialize (H _ _ _ _ H2 H3 H1) || specialize (H0 _ _ _ _ H2 H3 H1)); clear H1 H2 H3; smack) 
  end;
  match goal with 
  | [H1: gen_check_flags (E_Binary_Operation _ ?op ?e1 ?e2) ?checkflags, 
     H2: do_flagged_checks_on_binop ?checkflags ?op ?v1 ?v2 _,
     H3: do_run_time_check_on_binop ?op ?v1 ?v2 _ |- _] => 
      specialize (gen_check_flags_on_binop_completeness _ _ _ _ _ _ _ _ _ H3 H1 H2); smack
  end.
- match goal with
  | [H: compile2_flagged_exp _ _ |- _] => inversion H; clear H; smack
  end.
  match goal with
  | [H1: eval_expr _ _ _, H2: eval_expr_x _ _ _ |- _] => inversion H1; inversion H2; clear H1 H2; subst
  end;
  repeat progress match goal with
  | [H1: compile2_flagged_exp ?e ?e_flagged, H2: eval_expr _ ?e _, H3: eval_expr_x _ ?e_flagged _ |- _] => 
      specialize (H _ _ _ _ H2 H3 H1); clear H1 H2 H3; smack 
  end;
  match goal with 
  | [H1: gen_check_flags (E_Unary_Operation _ ?op ?e) ?checkflags, 
     H2: do_flagged_checks_on_unop ?checkflags ?op ?v _,
     H3: do_run_time_check_on_unop ?op ?v _ |- _] => 
      specialize (gen_check_flags_on_unop_completeness _ _ _ _ _ _ _ H3 H1 H2); smack
  end.
- match goal with
  | [H: compile2_flagged_name _ _ |- _] => inversion H; clear H; smack
  end.
  match goal with
  | [H1: eval_name _ _ _, H2: eval_name_x _ _ _ |- _] => inversion H1; inversion H2; clear H1 H2; smack
  end.
- match goal with
  | [H: compile2_flagged_name _ _ |- _] => inversion H; clear H; smack
  end.
  match goal with
  | [H1: eval_name _ _ _, H2: eval_name_x _ _ _ |- _] => inversion H1; inversion H2; clear H1 H2; smack
  end;
  repeat progress match goal with
  | [H1: compile2_flagged_exp ?e ?e_flagged, H2: eval_expr _ ?e _, H3: eval_expr_x _ ?e_flagged _ |- _] => 
      specialize (H _ _ _ _ H2 H3 H1); clear H1 H2 H3; smack 
  end;
  repeat progress match goal with 
    | [H1: Normal ?v1 = Normal ?v2 |- _] => inversion H; clear H; smack
    | [H1: STACK.fetchG ?i ?s = ?v1, H2: STACK.fetchG ?i ?s = ?v2 |- _ ] => rewrite H1 in H2; clear H1; smack 
    end;
  match goal with
  | [H1: gen_name_check_flags ?e ?checkflags, 
     H2: do_flagged_index_checks ?checkflags ?i ?l ?u _,
     H3: do_index_check ?i ?l ?u _ |- _] =>
       specialize (gen_index_check_flags_completeness _ _ _ _ _ _ _ _ _ _ H3 H1 H2); smack
  end.
- match goal with
  | [H: compile2_flagged_name _ _ |- _] => inversion H; clear H; smack
  end.
  match goal with
  | [H1: eval_name _ _ _, H2: eval_name_x _ _ _ |- _] => inversion H1; inversion H2; clear H1 H2; smack
  end.
Qed.
*)














