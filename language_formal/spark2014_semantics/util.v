(* function / lemma library *)
Require Export wellformed.

Ltac rm_eval_expr :=
    repeat match goal with
    | [ |- eval_expr _ (Evar _ _) _] => apply eval_Evar
    | [ |- eval_expr ?S (Ebinop _ _ _ _) _] => eapply eval_Ebinop
    | [h: eval_expr ?S ?E ?V |- eval_expr ?S ?E _] => apply h 
    | [h: ?V = eval_binop ?OP _ _ |- ?V = eval_binop ?OP _ _] => apply h
    | [h: ?A |- ?A] => apply h
    end.

Ltac simpl_binop :=
    match goal with
    | [ |- context [eval_binop ?OP (ValNormal ?V1) (ValNormal ?V2)]] => unfold eval_binop; simpl
(*
    | [ |- context [eval_binop Cne (ValInt ?V1) (ValInt ?V2)]] => unfold eval_binop; simpl
    | [ |- context [eval_binop Ceq (ValInt ?V1) (ValInt ?V2)]] => unfold eval_binop; simpl
    | [ |- context [eval_binop Oadd (ValInt ?V1) (ValInt ?V2)]] => unfold eval_binop; simpl
    | [ |- context [eval_binop Osub (ValInt ?V1) (ValInt ?V2)]] => unfold eval_binop; simpl
    | [ |- context [eval_binop Omul (ValInt ?V1) (ValInt ?V2)]] => unfold eval_binop; simpl
    | [ |- context [eval_binop Odiv (ValInt ?V1) (ValInt ?V2)]] => unfold eval_binop; simpl
    | [ |- context [eval_binop Oand (ValBool ?V1) (ValBool ?V2)]] => unfold eval_binop; simpl
    | [ |- context [eval_binop Oor (ValBool ?V1) (ValBool ?V2)]] => unfold eval_binop; simpl
*)
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

Ltac rm_wd_expr :=
    repeat match goal with
    | [ |- well_defined_expr _ (Econst _ ?C)] => destruct C; apply (WD_Econst_Bool, WD_Econst_Int)
    | [ |- well_defined_expr _ (Evar _ _)] => eapply WD_Evar;
          match goal with 
          [ h: Some ?V = fetch ?X ?S |- Some _ = fetch ?X ?S ] => apply h
          end
    | [ |- well_defined_expr ?S (Ebinop _ ?OP ?E1 ?E2)] => apply WD_Ebinop; specialize_hypo; assumption
    | [ |- well_defined_expr ?S (Eunop _ ?OP ?E)] => apply WD_Eunop; specialize_hypo; assumption
    | [ h: Some ?V = fetch ?X ?S |- well_defined_expr ?S (Evar _ ?X)] => destruct V; subst
    end.

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)

Ltac rm_exists :=
    repeat match goal with
    | [ h: exists _, _ |- _ ] => inversion h; clear h
    | [ h: _ /\ _  |- _ ] => inversion h; clear h
    end.







