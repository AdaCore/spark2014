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

Require Import List.
(* Functional Scheme lgth_ind := Induction for Datatypes.length Sort Prop. *)


Lemma length_invnil : forall A (l:list A), length l = 0 -> l = nil.
Proof.
  intros A l H.
  destruct l;auto;simpl in *.
  inversion H.
Qed.

Lemma length_invcons : forall A n (l:list A), length l = S n -> exists x l', l = x::l'.
Proof.
  intros A n l H.
  destruct l;auto;simpl in *.
  inversion H.
  exists a.
  exists l.
  reflexivity.
Qed.

Function split1 A n (l:list A) {struct n} :=
  match l,n with
    | _,O => Some(nil,l)
    | e::l' , S n'  =>
      match split1 A n' l' with
        | Some(l1,l2) => Some (e::l1,l2)
        | None => None
      end
    | nil, S _ => None
  end.

(* This should be a regular Definition but it makes Function bug
   later, this is a bug of Function that will be hopefukly fixed in
   next versions. *)
Definition split2 {A} n m (l:list A) :=
  match split1 A n l with
    | None => None
    | Some (l1,l2') =>
      match split1 A m l2' with
        | None => None
        | Some (l2,l3) => Some (l1,(l2,l3))
      end
  end.


Lemma split1_correct :
  forall A n (l l2 l1:list A),
    (split1 _ n l = Some (l1,l2))
    -> List.length l1 = n /\ (l = l1 ++ l2).
Proof.
  intros A n l.
  functional induction split1 A n l;simpl;intros.
  - inversion H.
    clear H.
    subst.
    simpl.
    split; reflexivity.
  - inversion H.
    clear H.
    subst.
    specialize (IHo _ _ e2).
    destruct IHo as [IHo1 IHo2].
    subst.
    split;reflexivity.
  - inversion H.
  - inversion H.
Qed.


Lemma split1_correct_eq :
  forall A n (l l2 l1:list A),
    (split1 _ n l = Some (l1,l2))
    -> (l = l1 ++ l2).
Proof.
  intros A n l l2 l1 H.
  apply (split1_correct A n l l2 l1) in H.
  destruct H;assumption.
Qed.

Lemma split1_correct_length :
  forall A n (l l2 l1:list A),
    (split1 _ n l = Some (l1,l2))
    -> List.length l1 = n.
Proof.
  intros A n l l2 l1 H.
  apply (split1_correct A n l l2 l1) in H.
  destruct H;assumption.
Qed.


Lemma split1_complete :
  forall A n (l l2 l1:list A),
    List.length l1 = n
    -> (l = l1 ++ l2)
    -> (split1 _ n l = Some (l1,l2)).
Proof.
  intros A n l.
  functional induction split1 A n l;simpl;intros.
  - rewrite (length_invnil _ _ H) in *.
    simpl in *.
    subst.
    reflexivity.
  - destruct (length_invcons _ _ _ H) as [e' l''].
    destruct l''.
    subst.
    simpl in *.
    inversion H; clear H.
    inversion H0. clear H0.
    subst.
    specialize (IHo l0 x refl_equal refl_equal).
    rewrite e2 in IHo.
    inversion IHo.
    reflexivity.
  - destruct l1.
    + simpl in *.
      discriminate.
    + simpl in *.
      inversion  H0.
      specialize (IHo l2 l1).
      rewrite IHo in e2;try discriminate.
      * inversion H.
        reflexivity.
      * assumption.
  - apply length_invcons in H.
    decompose [ex] H. clear H.
    subst.
    simpl in *.
    inversion H0.
Qed.

Lemma split2_correct :
  forall A n m (l l1 l2 l3:list A),
    split2 n m l = Some (l1,(l2,l3))
    -> (l = l1 ++ l2 ++ l3) /\ List.length l1 = n /\ List.length l2 = m.
Proof.
  intros A n m l l1 l2 l3 H.
  unfold split2 in H.
  destruct (split1 A n l) eqn:heq.
  - destruct p.
    apply split1_correct in heq.
    destruct heq as [heq1 heq2].
    subst l.
    destruct (split1 A m l4) eqn:heq'.
    + destruct p.
      inversion H;clear H;subst. 
      apply split1_correct in heq'.
      destruct heq' as [heq'1 heq'2].
      subst;auto.
    + inversion H.
  - inversion H.
Qed.





