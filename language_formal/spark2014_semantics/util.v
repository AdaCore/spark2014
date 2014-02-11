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


Ltac Rdiscriminate :=
  let rewd HH HH' y z :=
      match y with 
        | z => fail 
        | _ => rewrite HH in HH';discriminate
  end in
    match goal with
      | HH: ?x = ?y , HH': ?x = ?z |- _ => rewd HH HH' y z
      | HH: ?x = ?y , HH': ?z = ?x |- _ => rewd HH HH' y z 
      | HH: ?y = ?x , HH': ?x = ?z |- _ => symmetry in HH; rewd HH HH' y z
      | HH: ?y = ?x , HH': ?z = ?x |- _ => symmetry in HH; rewd HH HH' y z
    end.

Ltac destrEx :=
  repeat progress (match goal with
                     | h: ex _ |- _  =>
                       let k := fresh "k" in
                       let hk1 := fresh "hk" in
                       destruct (h) as [k hk1];try assumption
                   end).



(* This tactic is a generalization of inversion. We first rewrite with
   some equality about function f first, and then do inversion on the
   rewritten hypothesis. The tactic removes the inversed hypothesis at
   the end so this *should* never loop. *)
Ltac Rinversion f :=
  let rewinv h h' := rewrite h in h'; inversion h'; try clear h' ; subst in
  match goal with
    | H: f ?X = _ , H': context [f ?X] |- _ => rewinv H H'
    | H: f ?X ?Y = _ , H': context [ f ?X ?Y ] |- _ => rewinv H H'
    | H: f ?X ?Y ?Z = _ , H': context [ f ?X ?Y ?Z ] |- _ => rewinv H H'
    | H: f ?X ?Y ?Z ?U = _ , H': context [ f ?X ?Y ?Z ?U ] |- _ => rewinv H H'
    | H: f ?X ?Y ?Z ?U ?V = _ , H': context [ f ?X ?Y ?Z ?U ?V ] |- _ => rewinv H H'
    | H: f ?X ?Y ?Z ?U ?V ?W = _ , H': context [ f ?X ?Y ?Z ?U ?V ?W ] |- _ => rewinv H H'
    (* Same with a left to right equality *)
    | H: _ = f ?X , H': context [f ?X] |- _ => rewinv H H'
    | H: _ = f ?X ?Y , H': context [ f ?X ?Y ] |- _ => rewinv H H'
    | H: _ = f ?X ?Y ?Z , H': context [ f ?X ?Y ?Z ] |- _ => rewinv H H'
    | H: _ = f ?X ?Y ?Z ?U , H': context [ f ?X ?Y ?Z ?U ] |- _ => rewinv H H'
    | H: _ = f ?X ?Y ?Z ?U ?V , H': context [ f ?X ?Y ?Z ?U ?V ] |- _ => rewinv H H'
    | H: _ = f ?X ?Y ?Z ?U ?V ?W , H': context [ f ?X ?Y ?Z ?U ?V ?W ] |- _ => rewinv H H'
  end ; auto.
