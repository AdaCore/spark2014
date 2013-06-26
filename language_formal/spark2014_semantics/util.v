Require Export wellformed.

(** * Customized Tactics *)

Ltac rm_eval_expr :=
    repeat match goal with
    | [ |- eval_expr _ (Evar _ _) _] => apply eval_Evar
    | [ |- eval_expr ?S (Ebinop _ _ _ _) _] => eapply eval_Ebinop
    | [h: eval_expr ?S ?E ?V |- eval_expr ?S ?E _] => apply h 
    | [h: eval_binop ?OP _ _  = ?V |- eval_binop ?OP _ _ = ?V ] => apply h
    | [h: ?A |- ?A] => apply h
    end.

Ltac simpl_unop := 
    match goal with
    | [ |- context[eval_unop ?uop (ValNormal (Bool ?b))]] => unfold eval_unop; simpl
    end.

Ltac simpl_binop :=
    match goal with
    | [ |- context [eval_binop ?OP (ValNormal ?V1) (ValNormal ?V2)]] => unfold eval_binop; simpl
    end.

Ltac simpl_binop_hyp :=
    repeat match goal with
    | [h: Some ?T = binop_type ?OP ?T1 ?T1 |- _ ] => 
            unfold binop_type in h; simpl in h; inversion h; subst
    | [h: binop_type ?OP ?T1 ?T1 = Some ?T |- _ ] => 
            unfold binop_type in h; simpl in h; inversion h; subst
    | [h: ValNormal ?V = eval_binop ?OP (ValNormal _) (ValNormal _) |- _] =>
            unfold eval_binop in h; simpl in h; inversion h; subst
    | [h: eval_binop ?OP (ValNormal _) (ValNormal _) = ValNormal ?V |- _] =>
            unfold eval_binop in h; simpl in h; inversion h; subst
    end.

Ltac specialize_hypo := 
    repeat match goal with
    | [h: ?A, h1: ?A -> _ |- _] => specialize (h1 h)
    | [h: ?A, h1: ?A -> _ -> _ |- _] => specialize (h1 h)
    end.

Ltac rm_wt_expr :=
    repeat match goal with
    | [ |- well_typed_expr _ (Evar _ _) _] => apply WT_Evar
    | [ |- well_typed_expr _ (Eunop _ _ _) _] => eapply WT_Eunop
    | [ |- well_typed_expr _ (Ebinop _ ?OP ?E1 ?E2) ?T] => eapply WT_Ebinop (* it will generate some universal variables *)
    | [ h: well_typed_expr _ ?E ?T |- well_typed_expr _ ?E _ ] => apply h 
    | [ |- context[binop_type _ _ _]] => unfold binop_type; auto
    end.

(*
Ltac rm_wd_expr :=
    repeat match goal with
    | [ |- well_defined_expr _ (Econst _ ?C)] => destruct C; apply (WD_Econst_Bool, WD_Econst_Int)
    | [ |- well_defined_expr _ (Evar _ _)] => eapply WD_Evar;
          match goal with 
          [ h: fetch ?X ?S = Some ?V |- fetch ?X ?S = Some _ ] => apply h
          end
    | [ |- well_defined_expr ?S (Ebinop _ ?OP ?E1 ?E2)] => apply WD_Ebinop; specialize_hypo; assumption
    | [ |- well_defined_expr ?S (Eunop _ ?OP ?E)] => apply WD_Eunop; specialize_hypo; assumption
    | [ h: fetch ?X ?S = Some ?V |- well_defined_expr ?S (Evar _ ?X)] => destruct V; subst
    end.
*)

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)

Ltac put_in_context_as hname :=
    match goal with
    [ |- ?A /\ ?B ] => assert(hname: A)
    end.

Ltac rm_none_eq_some :=
    match goal with
    | [h: None = Some _ |- _ ] => inversion h
    | [h: Some _ = None |- _ ] => inversion h
    end.

Ltac rm_exists :=
    repeat match goal with
    | [ h: exists _, _ |- _ ] => inversion h; clear h
    | [ h: _ /\ _  |- _ ] => inversion h; clear h
    end.

Ltac rm_or_hyp := 
    match goal with
    | [h: ?b1 \/ ?b2 |- _] => inversion h; clear h
    end.

Ltac distr_qualifier := 
    match goal with
    [h: forall x: ?T, ?A1 /\ ?A2 |- _ ] => assert ((forall x: T, A1) /\ (forall x: T, A2))
            ; [split; intros xz; specialize (h xz); rm_exists; assumption | ]; clear h; rm_exists
    end.







