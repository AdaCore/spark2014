(** 
_AUTHOR_

<<
Zhi Zhang
Departmnt of Computer and Information Sciences
Kansas State University
zhangzhi@ksu.edu
>>
*)

(** * Customized Tactics *)

Ltac simpl_unop unfunc := 
    match goal with
    | [ |- context[unfunc ?uop (_ (_ ?b))]] => unfold unfunc; simpl
    end.

Ltac simpl_binop binfunc :=
    match goal with
    | [ |- context [binfunc ?OP (_ ?V1) (_ ?V2)]] => unfold binfunc; simpl
    end.

(* this for operation on type system *)
Ltac simpl_binop_hyp1 binfunc  :=
    repeat match goal with
    | [h: Some ?T = binfunc ?OP ?T1 ?T1 |- _ ] => 
            unfold binfunc in h; simpl in h; inversion h; subst
    | [h: binfunc ?OP ?T1 ?T1 = Some ?T |- _ ] => 
            unfold binfunc in h; simpl in h; inversion h; subst
    end.

(* this is for operation on values *)
Ltac simpl_binop_hyp2 binfunc  :=
    repeat match goal with
    | [h: ?ValNormal ?V = binfunc ?OP (?ValNormal _) (?ValNormal _) |- _] =>
            unfold binfunc in h; simpl in h; inversion h; subst
    | [h: binfunc ?OP (?ValNormal _) (?ValNormal _) = ?ValNormal ?V |- _] =>
            unfold binfunc in h; simpl in h; inversion h; subst
    end.

Ltac specialize_hypo := 
    repeat match goal with
    | [h: ?A, h1: ?A -> _ |- _] => specialize (h1 h)
    | [h: ?A, h1: ?A -> _ -> _ |- _] => specialize (h1 h)
    end.

(* prove some obviously true term, for example |- And <> Or *)
Ltac rm_always_true :=
    match goal with
    | |- ?A <> ?B => unfold not; let h := fresh "h" in intros h; inversion h
    end.

Ltac rm_false_hyp :=
    match goal with
    | h: ?A <> ?A |- _ => unfold not in h; intuition
    end.

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)

Ltac rm_eq :=
    match goal with
    [h: ?A _ = ?A _ |- _] => inversion h as [h1]; auto
    end.

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









