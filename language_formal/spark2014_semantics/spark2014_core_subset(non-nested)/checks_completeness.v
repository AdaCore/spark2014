Require Export semantics_flagged.
Require Export X_SparkTactics.


Scheme expression_ind := Induction for expression Sort Prop 
                         with name_ind := Induction for name Sort Prop.

Lemma gen_check_flags_on_binop_completeness: forall op v1 v2 v3 ast_num e1 e2 checkflags v3',
  do_run_time_check_on_binop op v1 v2 v3 ->
    gen_exp_check_flags (E_Binary_Operation ast_num op e1 e2) checkflags ->
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
    gen_exp_check_flags (E_Unary_Operation ast_num op e) checkflags ->
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

(** * Completeness Proof of Expression *)

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
  | [H1: gen_exp_check_flags (E_Binary_Operation _ ?op ?e1 ?e2) ?checkflags, 
     H2: do_flagged_checks_on_binop ?checkflags ?op ?v1 ?v2 _,
     H3: do_run_time_check_on_binop ?op ?v1 ?v2 _ |- _] => 
      specialize (gen_check_flags_on_binop_completeness _ _ _ _ _ _ _ _ _ H3 H1 H2); smack
  | [H1: gen_exp_check_flags (E_Unary_Operation _ ?op ?e) ?checkflags, 
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

Lemma copy_in_checks_completeness: forall params s f args f' params' args' f'' ,
  copy_in s f params args f' ->
    copy_in_x s f params' args' f'' ->
      compile2_flagged_parameter_specifications params params' ->
        compile2_flagged_exps args args' ->
          f' = f''.
Proof.
  induction params; smack.
- inversion H1; clear H1; subst.
  destruct args. 
  + inversion H2; clear H2; subst.
    inversion H; inversion H0; smack.
  + inversion H.
- destruct args, args', params';
  match goal with 
  | [H: copy_in _ _ (?a :: ?al) nil _ |- _] => inversion H
  | [H: copy_in _ _ nil (?a :: ?al) _ |- _] => inversion H
  | [H: copy_in_x _ _ nil (?a :: ?al) _ |- _] => inversion H
  | [H: compile2_flagged_exps (?a :: ?al) nil |- _] => inversion H
  | _ => idtac
  end.
  inversion H1; clear H1; subst.
  inversion H2; clear H2; subst.
  assert(HZ1: a.(parameter_name) = p.(parameter_name_x)).
    inversion H6; smack.
  assert(HZ2: a.(parameter_mode) = p.(parameter_mode_x)).
    inversion H6; smack.

  inversion H; clear H; subst;
  inversion H0; clear H0; smack;
  match goal with
  | [H1: eval_expr ?s ?e ?v,
     H2: eval_expr_x ?s ?e' ?v',
     H3: compile2_flagged_exp ?e ?e' |- _] => specialize (expression_checks_completeness _ _ _ _ _ H1 H2 H3); smack
  | _ => idtac
  end;
  match goal with
  | [H1: copy_in ?s ?f ?params ?args _, 
     H2: copy_in_x ?s ?f ?params' ?args' _, 
     H3: compile2_flagged_parameter_specifications ?params ?params', 
     H4: compile2_flagged_exps ?args ?args' |- _] => specialize (IHparams _ _ _ _ _ _ _ H1 H2 H3 H4); smack
  end.
Qed.

Lemma copy_out_checks_completeness: forall params s f args f' params' args' f'' ,
  copy_out s f params args f' ->
    copy_out_x s f params' args' f'' ->
      compile2_flagged_parameter_specifications params params' ->
        compile2_flagged_exps args args' ->
          f' = f''.
Proof.
  induction params; smack.
- inversion H1; clear H1; subst.
  destruct args. 
  + inversion H2; clear H2; subst.
    inversion H; inversion H0; smack.
  + inversion H.
- destruct args, args', params';
  match goal with 
  | [H: copy_out _ _ (?a :: ?al) nil _ |- _] => inversion H
  | [H: copy_out _ _ nil (?a :: ?al) _ |- _] => inversion H
  | [H: copy_out_x _ _ nil (?a :: ?al) _ |- _] => inversion H
  | [H: compile2_flagged_exps (?a :: ?al) nil |- _] => inversion H
  | _ => idtac
  end.
  inversion H1; clear H1; subst.
  inversion H2; clear H2; subst.
  assert(HZ1: a.(parameter_name) = p.(parameter_name_x)).
    inversion H6; smack.
  assert(HZ2: a.(parameter_mode) = p.(parameter_mode_x)).
    inversion H6; smack.

  inversion H; clear H; subst;
  inversion H0; clear H0; smack.
  rewrite HZ1 in *.
  inversion H5; inversion H7; smack. 
  repeat progress match goal with
  | [H1: STACK.fetch ?x ?f = _, H2: STACK.fetch ?x ?f = _ |- _] => rewrite H1 in H2; smack
  | [H1: STACK.updateG ?s ?x ?v = _ , H2: STACK.updateG ?s ?x ?v = _ |- _] => rewrite H1 in H2; smack
  end.
Qed.

Lemma declaration_checks_completeness: forall s f d f' d' f'',
  eval_decl s f d f' ->
    eval_decl_x s f d' f'' ->
      compile2_flagged_declaration d d' ->
        f' = f''. 
Proof.
  intros s f d f' d' f'' H; revert d' f'';
  induction H; intros;
  match goal with
  | [H: compile2_flagged_declaration _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: compile2_flagged_object_declaration _ _ |- _] => inversion H; clear H; smack
  | _ => idtac
  end;
  match goal with
  | [H: eval_decl_x _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  [ | | | | 
    specialize (IHeval_decl _ _ H9 H6); smack |
    specialize (IHeval_decl1 _ _ H10 H7); inversion IHeval_decl1
  ];
  match goal with
  | [H1: eval_expr ?s ?e _, 
     H2: eval_expr_x ?s ?e' _, 
     H3: compile2_flagged_exp ?e ?e' |- _] => 
       specialize (expression_checks_completeness _ _ _ _ _ H1 H2 H3); smack
  | [H1: eval_decl_x ?s ?f ?d1' ?f', H2: compile2_flagged_declaration ?d1 ?d1' |- _] =>
      specialize (IHeval_decl1 _ _ H10 H7); clear H1 H2; inversion IHeval_decl1
  end.
Qed.

Lemma store_update_checks_completeness: forall s x v s' x' s'',
  storeUpdate s x v s' ->
    storeUpdate_x s x' v s'' ->
      compile2_flagged_name x x' ->
        s' = s''.
Proof.
  intros;
  inversion H1; clear H1; subst;

  repeat progress match goal with
    | [H: gen_name_check_flags _ _ |- _] => inversion H; clear H; subst
    | [H: storeUpdate _ _ _ _ |- _] => inversion H; clear H; subst
    | [H: storeUpdate_x _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H1: eval_expr ?s ?e _, 
     H2: eval_expr_x ?s ?e' _, 
     H3: compile2_flagged_exp ?e ?e' |- _] => 
       specialize (expression_checks_completeness _ _ _ _ _ H1 H2 H3); clear H1 H2 H3; smack
  | _ => idtac
  end;
  repeat progress match goal with
    | [H1: STACK.fetchG ?i ?s = ?v1, H2: STACK.fetchG ?i ?s = ?v2 |- _ ] => rewrite H1 in H2; clear H1; smack 
    | [H: Normal _ = Normal _ |- _] => inversion H; clear H; subst
    | [H: do_flagged_index_checks _ _ _ _ _ |- _] => inversion H; clear H; smack 
    | [H: do_flagged_index_check _ _ _ _ _ |- _ ] => inversion H; clear H; smack
    | [H: do_index_check _ _ _ _ |- _] => inversion H; clear H; smack
  end.
Qed.

Lemma statement_assign_checks_completeness: forall st s ast_num x e s' st' x' e' s'',
  eval_stmt st s (S_Assignment ast_num x e) s' -> 
    eval_stmt_x st' s (S_Assignment_X ast_num x' e') s'' -> 
      compile2_flagged_stmt (S_Assignment ast_num x e) (S_Assignment_X ast_num x' e') ->
        compile2_flagged_symbol_table st st' ->
          s' = s''.
Proof.
  intros;
  match goal with
  | [H1: eval_stmt _ _ ?Assign _ , 
     H2: eval_stmt_x _ _ ?Assign' _, 
     H3: compile2_flagged_stmt ?Assign ?Assign' |- _] => 
      inversion H3; inversion H1; inversion H2; subst; clear H1 H2 H3
  end;
  repeat progress match goal with
  | [H1: eval_expr ?s ?e _, 
     H2: eval_expr_x ?s ?e' _, 
     H3: compile2_flagged_exp ?e ?e' |- _] => 
       specialize (expression_checks_completeness _ _ _ _ _ H1 H2 H3); clear H1 H2 H3; smack
  | [H1: storeUpdate ?s ?x ?v _, 
     H2: storeUpdate_x ?s ?x' ?v _, 
     H3: compile2_flagged_name ?x ?x' |- _] =>
      specialize (store_update_checks_completeness _ _ _ _ _ _ H1 H2 H3); clear H1 H2 H3; smack
  end.
Qed.

(** * Completeness Proof of Statement *)

Lemma statement_checks_completeness: forall st s stmt s' st' stmt' s'',
  eval_stmt st s stmt s' -> 
    eval_stmt_x st' s stmt' s'' -> 
      compile2_flagged_stmt stmt stmt' ->
        compile2_flagged_symbol_table st st' ->
          s' = s''.
Proof.
  intros st s stmt s' st' stmt' s'' H; revert st' stmt' s''.
  induction H; intros.
- repeat progress match goal with
    | [H: compile2_flagged_stmt _ _ |- _] => inversion H; clear H; smack
    | [H: eval_stmt_x _ _ _ _ |- _] => inversion H; clear H; smack
  end.
- match goal with
    | [H: compile2_flagged_stmt _ _ |- _] => inversion H; subst
  end.
  repeat progress match goal with 
    | [H: eval_expr _ _ (Run_Time_Error _) |- _] => 
        specialize (Eval_S_Assignment_RTE _ _ _ st ast_num x H); clear H; smack
    | [H1: eval_expr ?s _ (Normal ?v), H2: storeUpdate ?s _ ?v _ |- _] =>  
        specialize (Eval_S_Assignment _ _ _ _ _ st ast_num H1 H2); clear H1 H2; smack
    | [H1: eval_stmt _ _ _ _, 
       H2: eval_stmt_x _ _ _ _ ,
       H3: compile2_flagged_stmt _ _ ,
       H4: compile2_flagged_symbol_table _ _ |- _] => 
        specialize (statement_assign_checks_completeness _ _ _ _ _ _ _ _ _ _ H1 H2 H3 H4); smack
    end.
- match goal with
    | [H: compile2_flagged_stmt _ _ |- _] => inversion H; subst
  end.
  repeat progress match goal with 
    | [H: eval_expr _ _ (Run_Time_Error _) |- _] => 
        specialize (Eval_S_Assignment_RTE _ _ _ st ast_num x H); clear H; smack
    | [H1: eval_expr ?s _ (Normal ?v), H2: storeUpdate ?s _ ?v _ |- _] =>  
        specialize (Eval_S_Assignment _ _ _ _ _ st ast_num H1 H2); clear H1 H2; smack
    | [H1: eval_stmt _ _ _ _, 
       H2: eval_stmt_x _ _ _ _ ,
       H3: compile2_flagged_stmt _ _ ,
       H4: compile2_flagged_symbol_table _ _ |- _] => 
        specialize (statement_assign_checks_completeness _ _ _ _ _ _ _ _ _ _ H1 H2 H3 H4); smack
    end.
- (* If RTE *)
  match goal with
    | [H: compile2_flagged_stmt _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
    | [H: eval_stmt_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
    | [H1: eval_expr ?s ?e _, 
       H2: eval_expr_x ?s ?e' _, 
       H3: compile2_flagged_exp ?e ?e' |- _] => 
         specialize (expression_checks_completeness _ _ _ _ _ H1 H2 H3); clear H1 H2 H3; smack
  end.
- (* If True *)
  match goal with
    | [H: compile2_flagged_stmt _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
    | [H: eval_stmt_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
    | [H1: eval_expr ?s ?e _, 
       H2: eval_expr_x ?s ?e' _, 
       H3: compile2_flagged_exp ?e ?e' |- _] => 
         specialize (expression_checks_completeness _ _ _ _ _ H1 H2 H3); clear H1 H2 H3; smack
  end.
- (* If False *)
  match goal with
    | [H: compile2_flagged_stmt _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
    | [H: eval_stmt_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
    | [H1: eval_expr ?s ?e _, 
       H2: eval_expr_x ?s ?e' _, 
       H3: compile2_flagged_exp ?e ?e' |- _] => 
         specialize (expression_checks_completeness _ _ _ _ _ H1 H2 H3); clear H1 H2 H3; smack
  end.
- (* While RTE *)
  match goal with
    | [H: compile2_flagged_stmt _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
    | [H: eval_stmt_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
    | [H1: eval_expr ?s ?e _, 
       H2: eval_expr_x ?s ?e' _, 
       H3: compile2_flagged_exp ?e ?e' |- _] => 
         specialize (expression_checks_completeness _ _ _ _ _ H1 H2 H3); clear H1 H2 H3; smack
  end.
- (* While True RTE *)
  match goal with
    | [H: compile2_flagged_stmt _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
    | [H: eval_stmt_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
    | [H1: eval_expr ?s ?e _, 
       H2: eval_expr_x ?s ?e' _, 
       H3: compile2_flagged_exp ?e ?e' |- _] => 
         specialize (expression_checks_completeness _ _ _ _ _ H1 H2 H3); clear H1 H2 H3; smack
  end;
  match goal with
  | [H1: eval_stmt_x _ _ ?c' _, H2: compile2_flagged_stmt _ ?c', H3: compile2_flagged_symbol_table _ _ |- _] =>
      specialize (IHeval_stmt _ _ _ H1 H2 H3); smack
  end.
- (* While True *)
  match goal with
    | [H: compile2_flagged_stmt _ _ |- _] => inversion H; subst
  end;
  match goal with
    | [H: eval_stmt_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
    | [H1: eval_expr ?s ?e _, 
       H2: eval_expr_x ?s ?e' _, 
       H3: compile2_flagged_exp ?e ?e' |- _] => 
         specialize (expression_checks_completeness _ _ _ _ _ H1 H2 H3); smack
  end;
  match goal with
  | [H1: eval_stmt_x _ _ ?c' _, H2: compile2_flagged_stmt _ ?c', H3: compile2_flagged_symbol_table _ _ |- _] =>
      specialize (IHeval_stmt1 _ _ _ H1 H2 H3); smack
  end.
- (* While False *)
  match goal with
    | [H: compile2_flagged_stmt _ _ |- _] => inversion H; subst
  end;
  match goal with
    | [H: eval_stmt_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
    | [H1: eval_expr ?s ?e _, 
       H2: eval_expr_x ?s ?e' _, 
       H3: compile2_flagged_exp ?e ?e' |- _] => 
         specialize (expression_checks_completeness _ _ _ _ _ H1 H2 H3); smack
  end.
- (* Procedure Call Args RTE *)
  match goal with
    | [H: compile2_flagged_stmt _ _ |- _] => inversion H; subst
  end;
  match goal with
    | [H: eval_stmt_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
    | [H1: Symbol_Table_Module.fetch_proc ?p ?st = _,
       H2: Symbol_Table_Module_X.fetch_proc ?p ?st' = _, 
       H3: compile2_flagged_symbol_table ?st ?st' |- _] => 
        specialize (symbol_table_procedure_rel _ _ _ _ _ _ _ H1 H2 H3); smack
  end;
  match goal with
    | [H: compile2_flagged_procedure_declaration _ _ |- _] => 
        specialize (procedure_components_rel _ _ H); smack
  end;  
  match goal with
    | [H1: copy_in _ _ ?params ?args _, 
       H2: copy_in_x _ _ ?params' ?args' _, 
       H3: compile2_flagged_parameter_specifications ?params ?params',
       H4: compile2_flagged_exps ?args ?args' |- _] => 
         specialize (copy_in_checks_completeness _ _ _ _ _ _ _ _ H1 H2 H3 H4); smack
  end.
- (* Procedure Call Decls RTE *)
  match goal with
    | [H: compile2_flagged_stmt _ _ |- _] => inversion H; subst
  end;
  match goal with
    | [H: eval_stmt_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
    | [H1: Symbol_Table_Module.fetch_proc ?p ?st = _,
       H2: Symbol_Table_Module_X.fetch_proc ?p ?st' = _, 
       H3: compile2_flagged_symbol_table ?st ?st' |- _] => 
        specialize (symbol_table_procedure_rel _ _ _ _ _ _ _ H1 H2 H3); smack
  end;
  match goal with
    | [H: compile2_flagged_procedure_declaration _ _ |- _] => 
        specialize (procedure_components_rel _ _ H); smack
  end;
  match goal with
    | [H1: cut_until _ _ _ _, H2: cut_until _ _ _ _ |- _] => 
        specialize (cut_until_uniqueness _ _ _ _ _ _ H1 H2); smack
    | _ => idtac
  end;
  match goal with
    | [H1: copy_in _ _ ?params ?args _, 
       H2: copy_in_x _ _ ?params' ?args' _, 
       H3: compile2_flagged_parameter_specifications ?params ?params',
       H4: compile2_flagged_exps ?args ?args' |- _] => 
         specialize (copy_in_checks_completeness _ _ _ _ _ _ _ _ H1 H2 H3 H4); smack
  end;
  match goal with
    | [H1: eval_decl _ _ ?dl _, 
       H2: eval_decl_x _ _ ?dl' _,
       H3: compile2_flagged_declaration ?dl ?dl' |- _] =>
        specialize (declaration_checks_completeness _ _ _ _ _ _ H1 H2 H3); smack
  end.
- (* Procedure Call Body RTE *)
  match goal with
    | [H: compile2_flagged_stmt _ _ |- _] => inversion H; subst
  end;
  match goal with
    | [H: eval_stmt_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
    | [H1: Symbol_Table_Module.fetch_proc ?p ?st = _,
       H2: Symbol_Table_Module_X.fetch_proc ?p ?st' = _, 
       H3: compile2_flagged_symbol_table ?st ?st' |- _] => 
        specialize (symbol_table_procedure_rel _ _ _ _ _ _ _ H1 H2 H3); smack
  end;
  match goal with
    | [H: compile2_flagged_procedure_declaration _ _ |- _] => 
        specialize (procedure_components_rel _ _ H); smack
  end;
  match goal with
    | [H1: cut_until _ _ _ _, H2: cut_until _ _ _ _ |- _] => 
        specialize (cut_until_uniqueness _ _ _ _ _ _ H1 H2); smack
    | _ => idtac
  end;
  match goal with
    | [H1: copy_in _ _ ?params ?args _, 
       H2: copy_in_x _ _ ?params' ?args' _, 
       H3: compile2_flagged_parameter_specifications ?params ?params',
       H4: compile2_flagged_exps ?args ?args' |- _] => 
         specialize (copy_in_checks_completeness _ _ _ _ _ _ _ _ H1 H2 H3 H4); smack
  end;
  match goal with
    | [H1: eval_decl _ _ ?dl _, 
       H2: eval_decl_x _ _ ?dl' _,
       H3: compile2_flagged_declaration ?dl ?dl' |- _] => 
        specialize (declaration_checks_completeness _ _ _ _ _ _ H1 H2 H3); smack
  end.
  match goal with
    | [H1: eval_stmt_x _ _ _ _, 
       H2: compile2_flagged_stmt _ _, 
       H3: compile2_flagged_symbol_table _ _ |- _] =>
        specialize (IHeval_stmt _ _ _ H1 H2 H3); smack
  end.
- (* Procedure Call *)
  match goal with
    | [H: compile2_flagged_stmt _ _ |- _] => inversion H; subst
  end;
  match goal with
    | [H: eval_stmt_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
    | [H1: Symbol_Table_Module.fetch_proc ?p ?st = _,
       H2: Symbol_Table_Module_X.fetch_proc ?p ?st' = _, 
       H3: compile2_flagged_symbol_table ?st ?st' |- _] => 
        specialize (symbol_table_procedure_rel _ _ _ _ _ _ _ H1 H2 H3); smack
  end;
  match goal with
    | [H: compile2_flagged_procedure_declaration _ _ |- _] => 
        specialize (procedure_components_rel _ _ H); smack
  end;
  match goal with
    | [H1: cut_until _ _ _ _, H2: cut_until _ _ _ _ |- _] => 
        specialize (cut_until_uniqueness _ _ _ _ _ _ H1 H2); smack
    | _ => idtac
  end;
  match goal with
    | [H1: copy_in _ _ ?params ?args _, 
       H2: copy_in_x _ _ ?params' ?args' _, 
       H3: compile2_flagged_parameter_specifications ?params ?params',
       H4: compile2_flagged_exps ?args ?args' |- _] => 
         specialize (copy_in_checks_completeness _ _ _ _ _ _ _ _ H1 H2 H3 H4); smack
  end;
  match goal with
    | [H1: eval_decl _ _ ?dl _, 
       H2: eval_decl_x _ _ ?dl' _,
       H3: compile2_flagged_declaration ?dl ?dl' |- _] => 
        specialize (declaration_checks_completeness _ _ _ _ _ _ H1 H2 H3); smack
  end;
  match goal with
    | [H1: eval_stmt_x _ _ _ _, 
       H2: compile2_flagged_stmt _ _, 
       H3: compile2_flagged_symbol_table _ _ |- _] =>
        specialize (IHeval_stmt _ _ _ H1 H2 H3); smack
  end.
  repeat progress match goal with
    | [H: Normal _ = Normal _ |- _] => inversion H; subst; clear H; smack
    | [H1: length ?l = length _, H2: length ?l = length _ |- _] =>
        rewrite H1 in H2; smack
    | [H1: length ?m' = length ?m, 
       H2: ?l ++ ?m = ?l' ++ ?m' |- _] => 
        symmetry in H1; specialize (app_same_length_eq2 _ _ _ _ _ H1 H2); smack; clear H1 H2
    | [H1: copy_out _ _ ?params ?args _,
       H2: copy_out_x _ _ ?params' ?args' _,
       H3: compile2_flagged_parameter_specifications ?params ?params',
       H4: compile2_flagged_exps ?args ?args' |- _] => 
        specialize (copy_out_checks_completeness _ _ _ _ _ _ _ _ H1 H2 H3 H4); smack
  end.
- (* Sequence RTE *)
  match goal with
    | [H: compile2_flagged_stmt _ _ |- _] => inversion H; subst
  end;
  match goal with
    | [H: eval_stmt_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
    | [H1: eval_stmt_x _ _ ?c' _, 
       H2: compile2_flagged_stmt ?c ?c',
       H3: compile2_flagged_symbol_table _ _ |- _] => specialize (IHeval_stmt _ _ _ H1 H2 H3); smack
  end.
- (* Sequence *)
  match goal with
    | [H: compile2_flagged_stmt _ _ |- _] => inversion H; subst
  end;
  match goal with
    | [H: eval_stmt_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
    | [H1: eval_stmt_x _ _ ?c' _, 
       H2: compile2_flagged_stmt ?c ?c',
       H3: compile2_flagged_symbol_table _ _ |- _] => specialize (IHeval_stmt1 _ _ _ H1 H2 H3); smack
  end.
Qed.














