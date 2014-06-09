Require Import LibTactics.

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

Ltac default_rename_hyp th :=
  match th with
    | _ = _ => fresh "heq"
  end.

(* This tactic be redefined in each module, it should return a fresh
   name build from the type of (hypothesis) h. *)
Ltac rename_hyp := default_rename_hyp.

(* "marks" hypothesis h of the current goal by putting id(..) on top
   of there types. *)
Ltac id_ify h := let th := type of h in change (id th) in h.

(* Unmarking one hyp. *)
Ltac unid H :=
  match type of H with
    | id ?th => change th in H
  end.

(* Unmarking all hyps *)
Ltac unidall :=
  repeat match goal with
    | H: id ?th |- _ => change th in H
  end.

(* Renames all hypothesis using the current rename_hyp. It does not
   rename hypothesis already marked (i.e. of type (id _)). *)
Ltac rename_norm :=
  repeat match goal with
           | H:_ |- _ =>
             match type of H with
               | id _ => fail 1
               | ?th => let newname := rename_hyp th in
                        rename H into newname;
                        change (id th) in newname
             end
         end.



(* Mark all current hypothesis of the goal to prevent re-renaming hyps
   when calling renaming tactics multiple times. Typical use: mark all
   hyps but the one we want to destruct (say h), destruct h; rename
   all unmarked hyps except h.

   idall ; unid h; inversion h; try id_ify h; rename_norm; unidall.
 *)
Ltac idall :=
  repeat match goal with
           | H:_ |- _ =>
             match type of H with
               | id _ => fail 1
               | ?th => change (id th) in H
             end
         end.


(* hyp(h)? *)
Tactic Notation "rename_after" tactic(T) constr(h) :=
  idall; unid h; (T h) ; try id_ify h; rename_norm ; unidall.
Tactic Notation "!!" tactic(T) := idall; T ; rename_norm ; unidall.

(* decompose takes a special list of constr as argument *)
(* Tactic Notation "decomp" hyp(h) := idall; unid h; decompose [and ex or] h ; clear h; rename_norm ; unidall. *)
Tactic Notation "decomp" hyp(h) := rename_after (fun x => decompose [and ex or] x) h.

Tactic Notation "!induction" constr(h) := rename_after (fun x => induction x) h.
Tactic Notation "!functional" "induction" constr(h) :=
   !! (functional induction h).
(*   rename_after (fun x => functional induction x) h. *)
Tactic Notation "!functional" "inversion" constr(h) :=
  rename_after (fun x => functional inversion x) h.
Tactic Notation "!destruct" constr(h) := rename_after (fun x => destruct x) h.
Tactic Notation "!intros" := idall;intros;rename_norm;unidall.
(* Tactic Notation "!inversion" hyp(h) := rename_after (fun x => inverts x as) h. *)
Tactic Notation "!inversion" hyp(h) := rename_after (fun x => inversion x;subst) h.
(* Tactic Notation "!invclear" hyp(h) := rename_after (fun x => inverts x as;intros) h. *)
Tactic Notation "!invclear" hyp(h) := rename_after (fun x => inversion x;clear x;subst) h.



(*
Ltac r := fun T => (fun h => idall; unid h; (T h) ; try id_ify h; rename_norm ; unidall).
Tactic Notation "!!!" tactic(T) := (fun _ => idall; T ; rename_norm ; unidall).

Ltac xxxx h := induction h.
Ltac yyy T h := idall; unid h; (T h) ; try id_ify h; rename_norm ; unidall.

Tactic Notation "rrr" tactic(T) constr(h) :=
  idall; unid h; ((fun x => T x) h) ; try id_ify h; rename_norm ; unidall.


Lemma foo: forall x y z:nat, x =y -> y=z -> x=z.
Proof.
  intros x y z H H0.
  yyy xxxx H.
Qed.
 *)
