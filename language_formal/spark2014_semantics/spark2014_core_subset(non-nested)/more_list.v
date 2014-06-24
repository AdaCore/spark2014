Require Import List.

Section Non_Empty_List.

  Inductive nlist (A: Type) :=
    | NEnd: A -> nlist A
    | NCons: A -> nlist A -> nlist A.

  Arguments NEnd [A] _.
  Arguments NCons [A] _ _.

  Function append (A : Type) (l: nlist A) (a: A): nlist A := 
    match l with
      | NCons a1 l1 => NCons a1 (append A l1 a)
      | NEnd a1 => NCons a1 (NEnd a)
    end.

  Arguments append [A] _ _.

  Infix "::" := NCons (at level 60, right associativity) : nlist_scope.
  Infix "+++" := append (right associativity, at level 60) : nlist_scope.

End Non_Empty_List.

(* In a special module to avoid conflict *)
Module NListNotations.
  Notation " [ x ] " := (NEnd x) : nlist_scope.
End NListNotations.

Delimit Scope nlist_scope with nlist.


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

(** * List Split Operations *)

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

Function split2 {A} n m (l:list A) :=
  match split1 A n l with
    | None => None
    | Some (l1,l2') =>
      match split1 A m l2' with
        | None => None
        | Some (l2,l3) => Some (l1,(l2,l3))
      end
  end.

(** * List Split Lemmas *)

Lemma split2_equation1 :
  forall A n m e (l l1 l2 l3: list A),
  split2 n m l = Some (l1,(l2,l3))
  -> split2 (S n) m (e::l) = Some (e::l1 , (l2, l3)).
Proof.
  intros A n m e l l1 l2 l3 H.
  unfold split2.
  simpl.
  functional induction (split2 n m l);try discriminate.
  inversion H.
  rewrite e0.
  rewrite e1.
  subst.
  reflexivity.
Qed.

Lemma split2_equation2 :
  forall A m e (l l1 l2 l3: list A),
  split2 0 m l = Some (l1,(l2,l3))
  -> split2 0 (S m) (e::l) = Some (nil , (e::l2, l3)).
Proof.
  intros A m e l l1 l2 l3 H.
  unfold split2.
  simpl.
  unfold split2 in H.
  simpl in *.
  destruct l.
  - destruct (split1 A m nil).
    + destruct p.
      inversion H.
      reflexivity.
    + inversion H.
  - destruct (split1 A m (a :: l)).
    + destruct p.
      inversion H.
      reflexivity.
    + inversion H.
Qed.

Lemma split2_equation3 :
  forall A n m e (l l1 l2 l3: list A),
  split2 n m l = None
  -> split2 (S n) m (e::l) = None.
Proof.
  intros A n m e l l1 l2 l3 H.
  unfold split2.
  simpl.
  unfold split2 in H.
  destruct (split1 A n l).
  - destruct p.
    destruct (split1 A m l4).
    + destruct p.
      inversion H.
    + reflexivity.
  - reflexivity.
Qed.


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

Require Import Omega.

Lemma split2_length_ok :
  forall A (l:list A) n m,
  List.length l >= n+m
 -> split2 n m l <> None.
Proof.
  intros A l.
  induction l;simpl;intros n m h.
  - assert (n=0) by omega.
    assert (m=0) by omega.
    subst.
    unfold split2.
    simpl.
    discriminate.
  - destruct n.
    + destruct m.
      * unfold split2.
        simpl.
        discriminate.
      * intro abs.
        assert (h':length l >= 0 + m) by omega.
        generalize (IHl 0 m h').
        intro IHl'.
        unfold split2 in abs,IHl'.
        simpl in *.
        { destruct l;simpl in *.
          -destruct (split1 A m nil);simpl in *.
           + destruct p.
             inversion abs.
           + contradiction. 
          - destruct (split1 A m (a0 :: l));simpl in *.
            + destruct p.
              inversion abs.
            + contradiction. }
    + assert (h':length l >= n + m) by omega.
      generalize (IHl n m h').
      intro IHl'.
      unfold split2 in IHl'.
      unfold split2.
      simpl in *.
      destruct (split1 A n l);simpl in *.
      * destruct p.
        { destruct (split1 A m l1).
          - destruct p.
            discriminate.
          - assumption. }
      * assumption.
Qed.

Lemma app_same_length_eq :
  forall A (l l' m m': list A),
    length l = length l'
    -> l++m = l'++m' -> l = l'/\ m=m'.
Proof.
  intros A l.
  induction l;simpl in *;intros.
  - symmetry in H.
    apply length_invnil in H.
    subst.
    split;auto.
  - destruct l'.
    + simpl in H.
      inversion H.
    + specialize (IHl l' m m').
      simpl in *.
      inversion H0.
      inversion H.
      specialize (IHl H4 H3).
      destruct IHl.
      subst.
      split;auto.
Qed.

Lemma split2_complete :
  forall A n m (l l1 l2 l3:list A),
    l = l1 ++ l2 ++ l3
    -> List.length l1 = n
    -> List.length l2 = m
    -> split2 n m l = Some (l1,(l2,l3)).
Proof.
  intros A n m l l1 l2 l3 H H0 H1.
  destruct (split2 n m l) eqn:heq.
  - destruct p.
    destruct p.
    apply split2_correct in heq.
    decompose [and] heq.
    clear heq.
    subst.
    symmetry in H4.
    destruct (app_same_length_eq _ _ _ _ _ H4 H2).
    subst.
    symmetry in H5.
    destruct (app_same_length_eq _ _ _ _ _ H5 H0).
    subst.
    reflexivity.
  - destruct (split2_length_ok _ l n m).
    + rewrite H.
      repeat rewrite app_length.
      omega.
    + assumption.
Qed.

