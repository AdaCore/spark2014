Require Import List.
Require Import Arith.
Require Import ZArith.

Module Type ElementType.

Parameter Inline element_t : Set.

Parameter Inline witness_t : Set.

Parameter Inline witness : element_t -> witness_t.

Parameter Inline e_nl : element_t.

Parameter Inline eq_witness : witness_t -> witness_t -> Prop.

Parameter Inline beq_witness : witness_t -> witness_t -> bool.

Axiom beq_witness_refl : forall e : witness_t, beq_witness e e = true.

Axiom beq_witness_true : forall e1 : witness_t, forall e2 : witness_t,
beq_witness e1 e2 = true -> eq_witness e1 e2.

Axiom beq_witness_false : forall e1 : witness_t, forall e2 : witness_t,
beq_witness e1 e2 = false -> not (eq_witness e1 e2).

End ElementType.

Module Raw_List (X: ElementType).

Import X.

Definition cursor : Set := nat.

Definition Rlist : Set := List.list (cursor*element_t).

(*** HAS_ELEMENT ***)

Fixpoint has_element (l : Rlist) (cu : cursor) : bool :=
match l with
nil => false
| a :: ls => orb (beq_nat (fst a) cu) (has_element ls cu)
end.

Lemma in_has_element :
forall l : Rlist, forall cu : cursor,
(exists e, List.In (cu, e) l) -> has_element l cu = true.
intros l cu; induction l; simpl.
intros [_ H]; contradict H.
intros [e [H | H]]; apply Bool.orb_true_intro.
left; rewrite H; simpl; rewrite <- beq_nat_refl; reflexivity.
right; apply IHl; exists e; exact H.
Qed.

Lemma has_element_in :
forall l : Rlist, forall cu : cursor,
has_element l cu = true -> (exists e, List.In (cu, e) l).
intro l; induction l; simpl.
intros _ H; contradict H; apply Bool.diff_false_true.
intros cu H; apply Bool.orb_true_elim in H; destruct H as [H | H]. 
exists (snd a).
left; apply beq_nat_true in H; rewrite <- H;
rewrite <- surjective_pairing; reflexivity.
destruct (IHl cu H) as [e He]; exists e.
right; exact He.
Qed.

(*** WELL_FORMED ***)

Fixpoint well_formed (l : Rlist) : Prop :=
match l with
nil => True
| a :: ls => fst a > 0 /\ has_element ls (fst a) = false /\ well_formed (ls)
end.

(*** POSITION1 ***)

Fixpoint position1 (l : Rlist) (cu : cursor) (n : nat) : nat :=
match l with
nil => 0
| a :: ls => if beq_nat (fst a) cu then n else position1 ls cu (S n)
end.

Lemma position1_has_element :
forall l : Rlist,
forall n : cursor, forall m : cursor,
has_element l n = true -> m <= position1 l n m.
intros l; simpl; induction l; simpl.
intros n m HH; apply Bool.diff_false_true in HH; elim HH.
intros n m HH; apply Bool.orb_true_elim in HH;
destruct HH as [HH | HH].
apply beq_nat_true in HH;
rewrite HH; rewrite <- beq_nat_refl; apply le_refl.
case (beq_nat (fst a) n).
apply le_refl.
apply le_trans with (S m);
[apply lt_le_weak; apply lt_n_Sn |
exact (IHl n (S m) HH)].
Qed.

Lemma has_element_position1 :
forall l : Rlist,
forall n : cursor, forall m : cursor,
position1 l n m > 0 -> has_element l n = true.
intros l; simpl; induction l; simpl.
intros _ m HH; contradict HH; apply gt_irrefl.
intros n m.
case_eq (beq_nat (fst a) n); intros HH Hp.
apply Bool.orb_true_l.
rewrite (IHl n (S m) Hp); apply Bool.orb_true_r.
Qed.

Lemma position1_no_element :
forall l:Rlist,  well_formed l ->
forall n:nat, n > 0 -> position1 l 0 n = 0.
intros l Hwf n H.
symmetry; apply le_n_O_eq; apply not_gt.
intro HH; generalize (has_element_position1 l 0 n HH).
clear n HH H.
induction l; simpl.
intro HH; contradict HH; apply Bool.diff_false_true.
simpl in Hwf; destruct Hwf as [H1 [_ H3]].
case_eq (fst a);
[ intro H; contradict H1; rewrite H; apply gt_irrefl |].
intros n _ H; rewrite Bool.orb_false_l in H;
apply (IHl H3 H).
Qed.

Lemma position1_nth :
forall l:Rlist,  well_formed l ->
forall cu:cursor, forall m:nat,
has_element l cu = true -> m > 0 ->
fst(List.nth ((position1 l cu m) - m) l (0,e_nl)) = cu.
intros l H; simpl.
induction l.
simpl; intros cu m Hko; contradict Hko; apply Bool.diff_false_true.
simpl has_element; intros cu m HH Hs;
apply Bool.orb_true_elim in HH; destruct HH as [HH | HH].
apply beq_nat_true in HH;
rewrite <- HH; simpl; rewrite <- beq_nat_refl;
rewrite (minus_diag m); simpl; reflexivity.
simpl.
case_eq (beq_nat (fst a) cu); intro Heq.
rewrite <- (beq_nat_true (fst a) cu Heq).
rewrite (minus_diag m); simpl; reflexivity.
simpl in H; destruct H as [H1 [H2 H3]].
assert(0 < position1 l cu (S m) - m ).
apply lt_le_trans with 1.
apply gt_Sn_O.
rewrite <- (minus_diag m);
rewrite (minus_Sn_m m m (le_refl m));
apply minus_le_compat_r.
apply (position1_has_element l cu (S m)); simpl;
exact HH.
rewrite (S_pred (position1 l cu (S m) - m) 0 H).
rewrite <- (IHl H3 cu (S m) HH (gt_Sn_O m)) at 2.
assert (pred(position1 l cu (S m) - m) = position1 l cu (S m) - S m).
apply plus_minus; rewrite plus_Sn_m; rewrite plus_n_Sm;
rewrite <- (S_pred (position1 l cu (S m) - m) 0 H);
rewrite <- (le_plus_minus m (position1 l cu (S m)));
[ | apply le_trans with (S m);
[ | apply (position1_has_element l cu (S m))]]; auto.
rewrite H0; reflexivity.
Qed.

Lemma nth_position1 :
forall l:Rlist,  well_formed l ->
forall i : nat, forall m:nat,
i < List.length l ->
position1 l (fst(List.nth i l (0, e_nl))) m = i + m.
intros l H i; simpl; generalize l H; clear l H;
induction i; simpl; intros l H m.
case l; simpl.
intros Hi; 
contradict Hi; exact (gt_irrefl 0).
clear l H; intros a l H;
rewrite <- beq_nat_refl ; reflexivity.
generalize H; clear H; case l; clear l; simpl.
intros _ Hi;
contradict Hi; exact (le_not_gt 0 (S i) (le_O_n (S i))).
intros a l [H1 [H2 H3]] Hl.
apply lt_S_n in Hl.
case_eq (beq_nat (fst a) (fst (nth i l (0, e_nl)))); intro Hi.
contradict H2.
rewrite (beq_nat_true (fst a) (fst (nth i l (0, e_nl))) Hi).
rewrite in_has_element; [apply Bool.diff_true_false |];
exists (snd (nth i l (0, e_nl)));
rewrite <- surjective_pairing.
apply nth_In. exact Hl.
rewrite plus_n_Sm; apply (IHi l H3); exact Hl.
Qed.

Lemma position1_length :
forall (l : Rlist), forall (cu : cursor), forall (m : nat),
0 < m -> position1 l cu m < List.length l + m.
intros l cu.
induction l; simpl.
intros m HH; exact HH.
intros m Hm.
rewrite plus_n_Sm.
case (beq_nat (fst a) cu); simpl.
rewrite (plus_comm (List.length l) (S m));
apply le_plus_trans; apply le_refl.
apply IHl; apply lt_O_Sn.
Qed.

Lemma position1_eq :
forall l : Rlist,
forall cu : cursor, has_element l cu = true ->
forall n : nat, forall m : nat,
position1 l cu n + m = position1 l cu m + n.
intros l cu.
induction l; simpl.
intros Hko; contradict Hko; apply Bool.diff_false_true.
case (beq_nat (fst a) cu).
intros _ n m; apply plus_comm.
intros Hhe n m ; rewrite Bool.orb_false_l in Hhe.
apply eq_add_S; repeat (rewrite plus_n_Sm).
apply (IHl Hhe (S n) (S m)).
Qed.

(*** FIRST1 ***)

Definition first1 (l : Rlist) : cursor :=
match l with
nil => 0
| a :: _ => fst a
end.

Lemma first1_nth :
forall l : Rlist,
(first1 l) = fst(nth 0 l (0, e_nl)).
intros l; induction l; simpl;
reflexivity.
Qed.

(*** NEXT1 ***)

Fixpoint next1 (l : Rlist) (cu : cursor) :=
match l with
nil => 0
| a :: ls =>
if beq_nat (fst a) cu then first1 ls else next1 ls cu
end.

Lemma next1_has_element :
forall l : Rlist, forall cu : cursor,
has_element l cu = true -> 
cu <> fst(List.nth (pred (List.length l)) l (0, e_nl)) ->
has_element l (next1 l cu) = true.
intro l; induction l; simpl.
intros cu H _; exact H.
intros cu H; 
apply Bool.orb_prop in H; destruct H as [H | H].
apply beq_nat_true in H; rewrite H; rewrite <- beq_nat_refl.
case l; simpl.
intro HH; symmetry in H; contradict H; exact HH.
intros a0 ll; simpl; intro HH; rewrite <- beq_nat_refl.
apply Bool.orb_true_intro; right;
apply Bool.orb_true_l.
generalize H; clear H; case_eq l.
simpl; intros _ H; contradict H; apply Bool.diff_false_true.
intros aa ll Hal; simpl length; rewrite <- Hal.
case_eq (beq_nat (fst a) cu); intro HH; simpl.
intros _ _; apply Bool.orb_true_intro; right.
rewrite Hal; simpl; rewrite <- beq_nat_refl; apply Bool.orb_true_l.
intros H1 H2; apply Bool.orb_true_intro; right.
apply (IHl cu H1); rewrite Hal; simpl length; rewrite <- Hal.
rewrite <- pred_Sn; exact H2.
Qed.

Lemma next1_has_element_simpl :
forall l : Rlist, forall cu : cursor,
has_element l cu = true -> 
has_element l (next1 l cu) = true \/ next1 l cu = 0.
intros l cu; induction l; simpl.
intro Hko; contradict Hko; apply Bool.diff_false_true.
case (beq_nat (fst a) cu); simpl.
case (beq_nat (fst a) (first1 l));
[intros _; left; apply Bool.orb_true_l|].
intros _; rewrite Bool.orb_false_l; case l; simpl.
right; reflexivity.
intros aa ll;
rewrite <- beq_nat_refl; left; apply Bool.orb_true_l.
intros Hhe; apply IHl in Hhe; destruct Hhe as [Hhe|Hnil];
[left; rewrite Hhe; apply Bool.orb_true_r|right; exact Hnil].
Qed.

Lemma next1_nth :
forall l:Rlist, well_formed l ->
forall cu:cursor, forall i:nat,
cu = fst(List.nth i l (0, e_nl)) ->
next1 l cu = fst(List.nth (S i) l (0, e_nl)).
intros l Hwf cu; simpl; induction l; simpl.
intro i; case i; simpl; auto.
intro i; case i; simpl.
intro H; rewrite H; rewrite <- beq_nat_refl; case l; simpl;
intros; reflexivity.
clear i; intros i Hvcu.
simpl in Hwf; destruct Hwf as [Hp [Hhe Hwf]].
case_eq (beq_nat (fst a) cu); intro Heq.
case_eq (leb (List.length l) i); intro H.
apply leb_complete in H;
rewrite (nth_overflow l (0, e_nl) H) in Hvcu; simpl in Hvcu;
contradict Hp; apply beq_nat_true in Heq;
rewrite Heq; rewrite Hvcu; apply gt_irrefl.
apply leb_complete_conv in H.
apply (nth_In l (0,e_nl)) in H.
rewrite (surjective_pairing (nth i l (0, e_nl))) in H.
rewrite <- Hvcu in H; apply beq_nat_true in Heq; rewrite <- Heq in H.
contradict Hhe; rewrite in_has_element;
[apply Bool.diff_true_false | exists (snd (nth i l (0, e_nl))); exact H].
apply (IHl Hwf i Hvcu).
Qed.

Lemma next1_has_element_inv :
forall l : Rlist, well_formed l ->
forall cu : cursor, forall n, n > 0 ->
position1 l (next1 l cu) n > 0 ->
position1 l cu n > 0 /\ length l + n > 1 + position1 l cu n.
intros l H cu; simpl; induction l; simpl.
intros n _ Hko; contradict Hko; apply gt_irrefl.
case (beq_nat (fst a) cu).
intros n Hn; case_eq l; simpl.
case_eq (beq_nat (fst a) 0); intro Ha0.
destruct H as [Hko _]; contradict Hko; apply beq_nat_true in Ha0;
rewrite Ha0; apply gt_irrefl.
intros _ Hko; contradict Hko; apply gt_irrefl.
intros aa ll Hl; rewrite <- beq_nat_refl.
intros _; split; [exact Hn|].
apply gt_n_S; rewrite plus_comm; rewrite plus_n_Sm;
rewrite (plus_n_O n) at 2.
apply plus_gt_compat_l; apply gt_Sn_O.
case_eq (beq_nat (fst a) (next1 l cu)).
intro Hko; apply beq_nat_true in Hko; contradict Hko.
simpl in H; destruct H as [Hf [Hhe Hwf]].
clear IHl; induction l; simpl.
intro Hko; contradict Hf;
rewrite Hko; apply gt_irrefl.
simpl in Hhe;
apply Bool.orb_false_elim in Hhe; destruct Hhe as [_ Hhe].
case (beq_nat (fst a0) cu).
case_eq l; simpl.
intros _ Hko; contradict Hf;
rewrite Hko; apply gt_irrefl.
intros aa ll H; rewrite H in Hhe; simpl in Hhe;
apply Bool.orb_false_elim in Hhe; destruct Hhe as [Hhe _].
intro Hff; apply beq_nat_false in Hhe; contradict Hhe;
rewrite Hff; reflexivity.
simpl in Hwf; destruct Hwf as [_[_ Hwf]].
apply (IHl Hhe Hwf).
simpl in H; destruct H as [_[_ Hwf]].
intros _ n; rewrite plus_n_Sm.
intros _; apply (IHl Hwf (S n) (gt_Sn_O n)).
Qed.

(*** PREVIOUS1 ***)

Fixpoint previous1 (l : Rlist) (cu : cursor) (prev : cursor) :=
match l with
nil => 0
| a :: ls =>
let cu1 := fst a in
if beq_nat cu1 cu then prev else previous1 ls cu cu1
end.

Lemma previous1_has_element :
forall l : Rlist, forall cu : cursor, forall p : nat,
previous1 l cu p > 0 -> previous1 l cu p <> p -> 
has_element l (previous1 l cu p) = true.
intros l cu; induction l; simpl.
intros p H; contradict H; apply gt_irrefl.
case (beq_nat (fst a) cu).
intros p _ H; contradict H; reflexivity.
intros p H1 _.
case_eq (beq_nat (fst a) (previous1 l cu (fst a))); intro H.
apply Bool.orb_true_l.
apply Bool.orb_true_intro; right;
apply beq_nat_false in H;
apply (IHl (fst a) H1); intro HH;
rewrite HH in H; apply H; reflexivity.
Qed.

Lemma previous1_nth :
forall l:Rlist, well_formed l ->
forall cu:cursor,  cu > 0 ->
forall i:nat, forall n:cursor, i > 0 ->
cu = fst(List.nth i l (0, e_nl)) ->
previous1 l cu n = fst(List.nth (i-1) l (0, e_nl)).
intros l Hwf cu Hcu; simpl;
induction l; simpl.
intros i; case i;
[intros ii HH; contradict HH; apply gt_irrefl |];
intros ii n _ H; case (S ii -1); simpl in H; auto.
intro i; case i;
[intros ii HH; contradict HH; apply gt_irrefl|].
intros ii n _ Heq.
simpl in Hwf; destruct Hwf as [Hfst [Hhe Hwf]].
rewrite <- pred_of_minus; simpl.
case_eq (beq_nat (fst a) cu); intro H.
apply beq_nat_true in H.
(* Contradiction *)
contradict Hhe.
rewrite in_has_element; [apply Bool.diff_true_false|].
exists (snd (nth ii l (0, e_nl))).
rewrite H; rewrite Heq.
rewrite <- surjective_pairing.
apply nth_In.
apply lt_S_n; apply le_lt_n_Sm;
apply gt_le_S; apply not_le.
intro Hl.
apply (nth_overflow l (0, e_nl)) in Hl.
rewrite Hl in Heq; simpl in Heq.
generalize Hfst; rewrite H; rewrite Heq; apply gt_irrefl.
generalize Heq; clear i Heq.
case_eq ii.
intros HH; case l; simpl;
[intro Hko; contradict Hcu; rewrite Hko; apply gt_irrefl|
intros p l0 Hp; rewrite Hp; rewrite <- beq_nat_refl; reflexivity].
intros iii Hi Heq; rewrite <- Hi in Heq.
rewrite (pred_Sn iii); rewrite <- Hi;
rewrite pred_of_minus.
apply (IHl Hwf ii (fst a));
[rewrite Hi; apply gt_Sn_O | exact Heq].
Qed.

Lemma previous1_O :
forall (l : Rlist), well_formed l ->
forall (n : nat),
previous1 l 0 n = 0.
intros l H; induction l; simpl.
auto.
simpl in H; destruct H as [Hko [_ H]].
case_eq (beq_nat (fst a) 0); intros Heq n.
contradict Hko; apply beq_nat_true in Heq; rewrite Heq;
apply gt_irrefl.
apply IHl; exact H.
Qed.

(*** LAST1 ***)

Fixpoint last1 (l : Rlist) :=
match l with
nil => 0
| a :: nil => fst a
| _ :: ls => last1 ls
end.

Lemma last1_nth :
forall l : Rlist,
(last1 l) = fst(nth (pred (List.length l)) l (0, e_nl)).
intros l; induction l; simpl.
reflexivity.
case_eq l.
simpl; intros; reflexivity.
intros aa ll Hal; simpl List.length; rewrite <- Hal.
rewrite IHl; rewrite Hal at 1; simpl; reflexivity.
Qed.

Lemma position1_last1 :
forall l : Rlist, well_formed l ->
position1 l (last1 l) 1 = length l.
intros l H; rewrite last1_nth.
case_eq l.
simpl; reflexivity.
intros a ll Hla; rewrite <- Hla.
rewrite nth_position1; simpl;
[rewrite <- plus_n_Sm; rewrite <- plus_n_O; symmetry;
apply S_pred with 0; rewrite Hla; simpl; apply gt_Sn_O | apply H |
rewrite Hla; simpl; apply lt_n_Sn].
Qed.

(*** NEW ***)

Module Type New.

Parameter new : Rlist -> cursor.

Axiom new_has_element : forall l : Rlist, has_element l (new l) = false.

Axiom new_valid : forall l : Rlist, (new l) > O.

End New.

(*** MAX_CU ***)

Module New_Max : New.

Fixpoint max_cu (l : Rlist) (max : cursor) : cursor :=
match l with
nil => max
| a :: ls =>
let cu := fst a in
if leb max cu then max_cu ls cu else max_cu ls max
end.

Lemma max_sup : forall l : Rlist, forall cu : cursor,
cu <= max_cu l cu.
intro l. induction l.
intro; auto.
intro; simpl.
case_eq (leb cu (fst a)); intro HE.
apply le_trans with (fst a).
apply leb_complete ; exact HE.
apply IHl.
apply IHl.
Qed.

Lemma max_invar : forall l : Rlist, forall cu2 : cursor,
max_cu l cu2 = cu2 \/ has_element l (max_cu l cu2) = true.
intro l; induction l;
simpl; intros cu.
left; reflexivity.
case (leb cu (fst a));
[case_eq (beq_nat (max_cu l (fst a)) cu); intros HE;
[left; apply beq_nat_true; exact HE | right] | ].
destruct IHl with (fst a) as [IH1 | IH1]; rewrite IH1;
[ rewrite <- beq_nat_refl; apply Bool.orb_true_l | apply Bool.orb_true_r].
destruct IHl with cu as [IH1 | IH1];
[left; exact IH1 | right; rewrite IH1; apply Bool.orb_true_r].
Qed.

Lemma hm_max : forall l : Rlist, forall cu : cursor, forall m : cursor,
has_element l cu = true -> cu <= (max_cu l m).
intros l; induction l; simpl.
intros cu m H; contradict H; apply Bool.diff_false_true.
intros cu m H; apply Bool.orb_true_elim in H;
destruct H as [Heq | Hhe].
case_eq (leb m (fst a)); intro HH; apply beq_nat_true in Heq;
rewrite <- Heq.
apply max_sup.
apply lt_le_weak.
exact (le_gt_trans (max_cu l m) m (fst a)
(max_sup l m) (leb_complete_conv (fst a) m HH)).
case_eq (leb m (fst a)); intro HH;
apply IHl;
[exact Hhe | exact Hhe].
Qed.

Definition new (l : Rlist) : cursor :=
S(max_cu l 0).

Lemma new_has_element : forall l : Rlist, has_element l (new l) = false.
intro l;
apply Bool.not_true_is_false; intro H.
apply lt_irrefl with (new l).
unfold new at 2.
apply le_lt_n_Sm.
apply hm_max.
exact H.
Qed.

Lemma new_valid : forall l : Rlist, new l > O.
intro l;
unfold new; apply gt_Sn_O.
Qed.

End New_Max.

(*** ELEMENT1 ***)

Fixpoint element1 (l : Rlist) (cu : cursor) : element_t :=
match l with
nil => e_nl
| a :: ls => if beq_nat (fst a) cu then snd a else element1 ls cu
end.

Lemma element1_has_element :
forall (l : Rlist), forall (cu : cursor),
has_element l cu = false -> element1 l cu = e_nl.
intros l cu; induction l; simpl.
intros; reflexivity.
case (beq_nat (fst a) cu).
rewrite Bool.orb_true_l; intro H; contradict H;
apply Bool.diff_true_false.
rewrite Bool.orb_false_l; apply IHl.
Qed.

(*** EQUIVALENT1 ***)

Definition equivalent (l1 : Rlist) (l2 : Rlist) : Prop :=
length l1 = length l2 /\
forall cu : cursor,
has_element l1 cu = true ->
(has_element l2 cu = true /\ element1 l1 cu = element1 l2 cu).

Lemma equal_equivalent :
forall l1 l2 : Rlist, well_formed l1 -> well_formed l2 ->
(forall cu : cursor,
      position1 l1 cu 1 = position1 l2 cu 1 /\
      (position1 l1 cu 1 > 0 ->
       element1 l1 cu = element1 l2 cu)) ->
equivalent l1 l2.
unfold equivalent; intros l1 l2 Hwf1 Hwf2 Hcu;
split; [|intros cu Hhe].
apply le_antisym.
destruct (Hcu (last1 l1)) as [Hp _];
rewrite <- (position1_last1 l1 Hwf1); rewrite Hp.
apply le_S_n; rewrite (plus_n_O (length l2)); 
rewrite plus_n_Sm; apply position1_length; apply gt_Sn_O.
destruct (Hcu (last1 l2)) as [Hp _];
rewrite <- (position1_last1 l2 Hwf2); rewrite <- Hp.
apply le_S_n; rewrite (plus_n_O (length l1));
rewrite plus_n_Sm; apply position1_length; apply gt_Sn_O.
destruct (Hcu cu) as [Hp He].
apply (position1_has_element _ _ 1) in Hhe.
generalize (He Hhe); rewrite Hp in Hhe; clear He; intro He;
apply has_element_position1 in Hhe.
split; [exact Hhe|exact He].
Qed.

(*** FIND1 ***)

Fixpoint find (l : Rlist) (e : witness_t) : cursor :=
match l with
nil => 0
| a :: ls => if beq_witness (witness(snd a)) e then fst a
else find ls e
end.

Lemma find_position1 :
forall l : Rlist, forall e : witness_t,
forall n : nat, n > 0 ->
position1 l (find l e) n = 0 -> find l e = 0.
intro l; induction l; simpl.
intros; reflexivity.
intros e n Hn; case (beq_witness (witness(snd a)) e).
rewrite <- beq_nat_refl; intros Hko; contradict Hn;
rewrite Hko; apply gt_irrefl.
case (beq_nat (fst a) (find l e)).
intros Hko; contradict Hn; rewrite Hko; apply gt_irrefl.
apply IHl; apply gt_Sn_O.
Qed.

Lemma find_has_element :
forall l : Rlist, forall e : witness_t,
has_element l (find l e) = true \/ (find l e = 0).
intro l; induction l; simpl.
intros; right; reflexivity.
intro e; case (beq_witness (witness(snd a)) e).
left; rewrite <- beq_nat_refl; apply Bool.orb_true_l.
destruct (IHl e) as [H | H].
left; rewrite H; apply Bool.orb_true_r.
right; exact H.
Qed.

Lemma find_element1 :
forall l : Rlist, forall e : witness_t,
forall n : nat, n > 0 -> well_formed l ->
position1 l (find l e) n > 0 ->
eq_witness (witness(element1 l (find l e))) e.
intro l; induction l; simpl.
intros e n _ _ Hko; contradict Hko; apply gt_irrefl.
intros e n Hn [Hfst [Hhe Hwf]];
case_eq (beq_witness (witness(snd a)) e); intro Heq.
rewrite <- beq_nat_refl; intros;
apply beq_witness_true in Heq; exact Heq.
case_eq (beq_nat (fst a) (find l e)); intro Heqn.
destruct (find_has_element l e) as [H | H].
apply beq_nat_true in Heqn; rewrite Heqn in Hhe; rewrite Hhe in H;
contradict H; apply Bool.diff_false_true.
apply beq_nat_true in Heqn; rewrite <- Heqn in H;
contradict Hfst; rewrite H; apply gt_irrefl.
apply (IHl e (S n) (gt_Sn_O n) Hwf).
Qed.

Lemma find_element1_rev :
forall l : Rlist, forall cu : cursor,
forall n : nat, n > 0 ->
position1 l cu n > 0 ->
position1 l (find l (witness(element1 l cu))) n > 0.
intros l cu; induction l; simpl.
intros n _ Hko; contradict Hko; apply gt_irrefl.
intros n Hn;
case (beq_nat (fst a) cu).
rewrite beq_witness_refl; rewrite <- beq_nat_refl;
intros; exact Hn.
case (beq_witness (witness (snd a)) (witness (element1 l cu))).
rewrite <- beq_nat_refl; intros; exact Hn.
case (beq_nat (fst a) (find l (witness (element1 l cu)))).
intros; exact Hn.
apply (IHl _ (gt_Sn_O n)).
Qed.

Lemma find_is_first1_gen :
forall l : Rlist,
forall e : witness_t, forall cun : cursor,
forall n : nat, n > 0 ->
position1 l (find l e) n > position1 l cun n ->
position1 l cun n > 0 ->
not (eq_witness (witness(element1 l cun)) e).
intros l; induction l; simpl.
intros e _ n _ _ H; contradict H; apply gt_irrefl.
intros e cu n Hn.
case_eq (beq_witness (witness(snd a)) e); intro He_eq; simpl.
(* CONTRADICTION *)
rewrite <- beq_nat_refl; simpl.
case (beq_nat (fst a) cu); simpl.
intro H; contradict H; apply gt_irrefl.
intros H Hhl; contradict H.
apply le_not_gt; apply le_trans with (S n);
[ apply le_n_Sn |
apply (position1_has_element l cu (S n)
(has_element_position1 l cu (S n) Hhl))].
case_eq (beq_nat (fst a) cu); intro Hcu_eq; simpl.
intros; apply beq_witness_false in He_eq; exact He_eq.
case (beq_nat (fst a) (find l e)).
intros H Hhl; contradict H.
apply le_not_gt; apply le_trans with (S n);
[ apply le_n_Sn |
apply (position1_has_element l cu (S n)
(has_element_position1 l cu (S n) Hhl))].
intros Hs1 Hs2.
apply (IHl e cu (S n) (gt_Sn_O n) Hs1 Hs2).
Qed.

Lemma find_is_first1_O :
forall l : Rlist,
forall e : witness_t, forall cun : cursor,
forall n : nat, n > 0 ->
position1 l (find l e) n = 0 ->
position1 l cun n > 0 -> not (eq_witness (witness(element1 l cun)) e).
intros l; induction l; simpl.
intros e _ n _ _ H; contradict H; apply gt_irrefl.
intros e cu n Hn.
case_eq (beq_witness (witness(snd a)) e); intro He_eq; simpl.
rewrite <- beq_nat_refl; simpl.
case (beq_nat (fst a) cu); simpl.
intros H1 H2; contradict H2; rewrite H1; apply gt_irrefl.
intros H _; contradict Hn; rewrite H; apply gt_irrefl.
case_eq (beq_nat (fst a) cu); intro Hcu_eq; simpl.
intros; apply beq_witness_false in He_eq; exact He_eq.
case (beq_nat (fst a) (find l e)).
intros H; contradict Hn; rewrite H; apply gt_irrefl.
intros Hs1 Hs2.
apply (IHl e cu (S n) (gt_Sn_O n) Hs1 Hs2).
Qed.

(*** LEFT1 ***)

Fixpoint left1 (l : Rlist) (cu : cursor) : Rlist :=
match l with
nil => nil
| a :: ls => if beq_nat (fst a) cu then nil else a :: (left1 ls cu)
end.

Lemma has_element_left1 :
forall l : Rlist, forall cu1 cu2 : cursor,
has_element (left1 l cu1) cu2 = true -> has_element l cu2 = true.
intros l cu1 cu2; induction l; simpl.
intro H; exact H.
case (beq_nat (fst a) cu1); simpl.
intro H; contradict H; apply Bool.diff_false_true.
case (beq_nat (fst a) cu2).
intros _; apply Bool.orb_true_l.
intro H; rewrite Bool.orb_false_l; rewrite Bool.orb_false_l in H.
apply (IHl H).
Qed.

Lemma WF_left1 :
forall l : Rlist, well_formed l ->
forall cu : cursor,
well_formed (left1 l cu).
intro l; induction l; simpl.
auto.
intros [Hfst [Hhe Hwf]] cu.
case (beq_nat (fst a) cu); simpl.
auto.
split.
exact Hfst.
split.
case_eq (has_element (left1 l cu) (fst a)); intro Hko;
[|reflexivity].
rewrite <- Hhe; symmetry;
apply (has_element_left1 l cu (fst a) Hko).
apply (IHl Hwf cu).
Qed.

Lemma left1_O :
forall l : Rlist, well_formed l ->
left1 l O = l.
induction l; simpl.
reflexivity.
intros [Hfst [_ Hwf]]; case_eq(beq_nat (fst a) O);
[intro Heq; apply beq_nat_true in Heq; contradict Hfst;
rewrite Heq; apply gt_irrefl|intros _].
rewrite (IHl Hwf); reflexivity.
Qed.

Lemma left1_length : 
forall (l : Rlist),
forall (cu : cursor), forall n : nat, n > 0 ->
position1 l cu n > 0 -> length (left1 l cu) = position1 l cu n - n.
intros l cu; induction l; simpl.
intros; reflexivity.
intro n; case (beq_nat (fst a) cu); simpl.
intros; symmetry; apply minus_diag.
intros Hn Hpos; rewrite (IHl (S n) (gt_Sn_O n) Hpos).
rewrite (minus_plus_simpl_l_reverse (position1 l cu (S n)) n 1).
rewrite (plus_Sn_m 0 n); rewrite plus_O_n.
rewrite plus_Sn_m; rewrite plus_O_n.
rewrite minus_Sn_m; [reflexivity |].
apply (has_element_position1 l cu (S n)) in Hpos.
apply (position1_has_element l cu (S n) Hpos).
Qed.

Lemma left1_position1_out :
forall (l : Rlist),
forall (cu : cursor), forall (n : nat), n > 0 ->
position1 l cu n > 0 ->
forall (cun : cursor), position1 l cu n <= position1 l cun n ->
position1 (left1 l cu) cun n = 0.
intros l cu; induction l; simpl.
intros; reflexivity.
intros n Hn; case (beq_nat (fst a) cu).
intros; reflexivity.
intros  Hpos cun; simpl;
case (beq_nat (fst a) cun); simpl.
intro Hko; contradict Hko.
apply gt_not_le; apply le_S_gt.
apply (has_element_position1 l cu (S n)) in Hpos.
apply (position1_has_element l cu (S n) Hpos).
apply (IHl (S n) (gt_Sn_O n) Hpos cun).
Qed.

Lemma left1_position1_in :
forall (l : Rlist),
forall (cu : cursor), forall (n : nat), n > 0 ->
position1 l cu n > 0 ->
forall (cun : cursor), position1 l cu n > position1 l cun n ->
position1 (left1 l cu) cun n = position1 l cun n.
intros l cu; induction l; simpl.
intros; reflexivity.
intros n Hn; case (beq_nat (fst a) cu).
intros _ cun; case (beq_nat (fst a) cun); intro Hko;
[contradict Hko; apply gt_irrefl |]; simpl.
case_eq (has_element l cun); intro Hhe.
contradict Hko; apply le_not_gt;
apply (le_trans n (S n) (position1 l cun (S n)) (le_n_Sn n)).
apply (position1_has_element l cun (S n) Hhe).
destruct (gt_O_eq (position1 l cun (S n))) as [Hs | Hs];
[rewrite (has_element_position1 l cun (S n) Hs)
in Hhe; contradict Hhe; apply Bool.diff_true_false | exact Hs].
intros  Hpos cun; simpl;
case (beq_nat (fst a) cun); simpl.
intros; reflexivity.
apply (IHl (S n) (gt_Sn_O n) Hpos cun).
Qed.

Lemma left1_element1_in :
forall (l : Rlist),
forall (cu : cursor), forall (n : nat), n > 0 ->
position1 l cu n > 0 ->
forall (cun : cursor), position1 l cu n > position1 l cun n ->
element1 (left1 l cu) cun = element1 l cun.
intros l cu; induction l; simpl.
intros; reflexivity.
intros n Hn; case (beq_nat (fst a) cu).
intros _ cun; case (beq_nat (fst a) cun); intro Hko;
[contradict Hko; apply gt_irrefl |]; simpl.
case_eq (has_element l cun); intro Hhe.
contradict Hko; apply le_not_gt;
apply (le_trans n (S n) (position1 l cun (S n)) (le_n_Sn n)).
apply (position1_has_element l cun (S n) Hhe).
rewrite (element1_has_element l cun Hhe); reflexivity.
intros  Hpos cun; simpl;
case (beq_nat (fst a) cun); simpl.
intros; reflexivity.
apply (IHl (S n) (gt_Sn_O n) Hpos cun).
Qed.

(*** RIGH1 ***)

Fixpoint right1 (l : Rlist) (cu : cursor) : Rlist :=
match l with
nil => nil
| a :: ls => if beq_nat (fst a) cu then l else right1 ls cu
end.

Lemma has_element_right1 :
forall l : Rlist, forall cu1 cu2 : cursor,
has_element (right1 l cu1) cu2 = true -> has_element l cu2 = true.
intros l cu1 cu2; induction l; simpl.
intro H; exact H.
case (beq_nat (fst a) cu1); simpl.
intro H; exact H.
intro H; rewrite (IHl H); apply Bool.orb_true_r.
Qed.

Lemma right1_has_element :
forall l : Rlist,
forall cu1 cu2 : cursor,
forall n : nat, n > 0 -> position1 l cu1 n > 0 ->
position1 l cu1 n <= position1 l cu2 n ->
has_element (right1 l cu1) cu2 = true.
intros l cu1 cu2; induction l; simpl.
intros n _ H; contradict H; apply gt_irrefl.
case (beq_nat (fst a) cu1); simpl.
intros n Hn _;
case (beq_nat (fst a) cu2); simpl;
[intros; reflexivity | intro HH].
apply (has_element_position1 l cu2 (S n)
(le_gt_trans (position1 l cu2 (S n)) n 0 HH Hn)).
intros n Hn Hpos;
case (beq_nat (fst a) cu2); simpl.
intro Hko;
apply (has_element_position1 l cu1 (S n)) in Hpos.
contradict Hko; apply gt_not_le; apply le_S_gt.
apply (position1_has_element l cu1 (S n) Hpos).
apply (IHl (S n) (gt_Sn_O n) Hpos).
Qed.

Lemma WF_right1 :
forall l : Rlist, well_formed l ->
forall cu : cursor,
well_formed (right1 l cu).
intros l Hwf; induction l; simpl.
auto.
intros cu; case (beq_nat (fst a) cu).
exact Hwf.
simpl in Hwf; destruct Hwf as [_ [_ Hwf]].
apply (IHl Hwf cu).
Qed.

Lemma right1_O :
forall l : Rlist, well_formed l ->
right1 l O = nil.
induction l; simpl.
reflexivity.
intros [Hfst [_ Hwf]]; case_eq(beq_nat (fst a) O);
[intro Heq; apply beq_nat_true in Heq; contradict Hfst;
rewrite Heq; apply gt_irrefl|intros _].
rewrite (IHl Hwf); reflexivity.
Qed.

Lemma right1_length : 
forall (l : Rlist),
forall (cu : cursor), forall n : nat, n > 0 ->
position1 l cu n > 0 ->
length (right1 l cu) = length l + n - position1 l cu n.
intros l cu; induction l; simpl.
intros n _ Hko; contradict Hko; apply gt_irrefl.
intros n Hn; case (beq_nat (fst a) cu); simpl.
intros _; case n.
rewrite <- plus_n_O; reflexivity.
intro m; rewrite <- plus_n_Sm; rewrite <- plus_Sn_m.
rewrite (minus_n_O (S (length l))) at 1.
rewrite (minus_plus_simpl_l_reverse (S (length l)) 0 m).
rewrite (plus_comm m (S(length l))); rewrite <- plus_n_O.
reflexivity.
case_eq (position1 l cu (S n));
[intros _ Hko; contradict Hko; apply gt_irrefl |].
intros m Heq Hpos; rewrite <- Heq in Hpos.
rewrite (IHl (S n) (gt_Sn_O n) Hpos); rewrite Heq.
rewrite <- plus_n_Sm.
rewrite (minus_plus_simpl_l_reverse (length l + n) m 1).
rewrite plus_Sn_m; rewrite plus_Sn_m.
rewrite plus_O_n; rewrite plus_O_n.
reflexivity.
Qed.

Lemma right1_position1_out :
forall (l : Rlist), well_formed l ->
forall (cu : cursor), forall (n : nat), n > 0 ->
position1 l cu n > 0 ->
forall (cun : cursor), position1 l cu n > position1 l cun n ->
position1 (right1 l cu) cun 1 = 0.
intros l Hwf cu;
induction l; simpl.
intros; reflexivity.
simpl in Hwf; destruct Hwf as [_ [Hhfst Hwf]];
intros n Hn; case (beq_nat (fst a) cu); simpl.
intros _ cun; case (beq_nat (fst a) cun);
[intro Hko; contradict Hko; apply gt_irrefl|].
intro Hpos; destruct (gt_O_eq (position1 l cun 2)) as [Hhe | Hhe].
contradict Hpos; apply le_not_gt.
apply (le_trans n (S n) (position1 l cun (S n)) (le_n_Sn n)).
apply (position1_has_element l cun (S n)
(has_element_position1 l cun 2 Hhe)).
symmetry; exact Hhe.
intros Hpos cun; case_eq (beq_nat (fst a) cun); intro Heq.
intros _; apply beq_nat_true in Heq.
rewrite <- Heq.
destruct (gt_O_eq (position1 (right1 l cu) (fst a) 1)) as [Hp|Hp];
[| symmetry; exact Hp].
apply (has_element_position1 (right1 l cu)
(fst a) 1) in Hp.
rewrite (has_element_right1 l cu (fst a) Hp) in Hhfst;
contradict Hhfst; apply has_element_in in Hp;
apply Bool.diff_true_false.
apply (IHl Hwf (S n) (gt_Sn_O n) Hpos cun).
Qed.

Lemma right1_position1_in :
forall (l : Rlist),
forall (cu : cursor), forall (n : nat), n > 0 ->
position1 l cu n > 0 ->
forall (cun : cursor), position1 l cu n <= position1 l cun n ->
position1 (right1 l cu) cun n + position1 l cu n = position1 l cun n + n.
intros l cu; induction l; simpl.
intros n _ Hko; contradict Hko; apply gt_irrefl.
intros n Hn; case (beq_nat (fst a) cu); simpl.
intros; reflexivity.
intros  Hpos cun; simpl;
case (beq_nat (fst a) cun); simpl.
intro Hko; contradict Hko; apply gt_not_le; apply le_S_gt.
apply (has_element_position1 l cu (S n)) in Hpos.
apply (position1_has_element l cu (S n) Hpos).
case_eq (has_element (right1 l cu) cun); intros Hhe Hp.
apply eq_add_S; rewrite (plus_n_Sm _ n).
rewrite <- (IHl (S n) (gt_Sn_O n) Hpos cun Hp).
rewrite <- plus_Sn_m; assert (S(position1 (right1 l cu) cun n) =
position1 (right1 l cu) cun (S n)); [|rewrite H; reflexivity].
apply (plus_reg_l _ _ n); repeat (rewrite (plus_comm n _)).
rewrite plus_Sn_m; rewrite plus_n_Sm.
apply (position1_eq _ _ Hhe).
rewrite (right1_has_element l cu cun (S n) (gt_Sn_O n) Hpos Hp) in Hhe.
contradict Hhe; apply Bool.diff_true_false.
Qed.

Lemma right1_element1_in :
forall (l : Rlist),
forall (cu : cursor), forall (n : nat), n > 0 ->
position1 l cu n > 0 ->
forall (cun : cursor), position1 l cu n <= position1 l cun n ->
element1 (right1 l cu) cun = element1 l cun.
intros l cu; induction l; simpl.
intros; reflexivity.
intros n Hn; case (beq_nat (fst a) cu).
intros; reflexivity.
intros  Hpos cun; simpl;
case (beq_nat (fst a) cun); simpl.
intro Hko;
apply (has_element_position1 l cu (S n)) in Hpos.
contradict Hko; apply gt_not_le; apply le_S_gt.
apply (position1_has_element l cu (S n) Hpos).
apply (IHl (S n) (gt_Sn_O n) Hpos cun).
Qed.

(*** INSERT1 ***)

Fixpoint insert1 (l : Rlist) (before : cursor)
(new : cursor) (e : element_t) : Rlist :=
match l with
nil => (new, e) :: nil
| a :: ls =>
if beq_nat (fst a) before then (new, e) :: l
else a :: (insert1 ls before new e)
end.

Lemma insert1_has_element : forall l : Rlist, forall cu : cursor,
forall e : element_t, forall cu2 : cursor, forall cu1 : cursor,
has_element l cu2 = true ->
has_element (insert1 l cu cu1 e) cu2 = true.
intro l; induction l; simpl.
intros _ _ cu2 cu1 Hko;
contradict Hko; apply Bool.diff_false_true.
intros cu e cu1 cu2.
case (beq_nat (fst a) cu); simpl.
intro H; rewrite H; apply Bool.orb_true_r.
intros H; apply Bool.orb_true_elim in H; destruct H as [H | H].
rewrite H; apply Bool.orb_true_l.
rewrite (IHl _ _ _ _ H); apply Bool.orb_true_r.
Qed.

Lemma has_element_insert1 : forall l : Rlist, forall cu : cursor,
forall e : element_t, forall cu2 : cursor, forall cu1 : cursor,
has_element (insert1 l cu cu1 e) cu2 = true ->
cu1 = cu2 \/ has_element l cu2 = true.
intro l; induction l; simpl.
intros _ _ cu2 cu1.
intro H;  rewrite Bool.orb_false_r in H; left;
apply beq_nat_true; exact H.
intros cu e cu1 cu2.
case (beq_nat (fst a) cu); simpl.
intros H; apply Bool.orb_true_elim in H; destruct H as [H | H];
[left; apply beq_nat_true; exact H | rewrite H; right; reflexivity].
intros H; apply Bool.orb_true_elim in H; destruct H as [H | H].
right; rewrite H; apply Bool.orb_true_l.
destruct (IHl cu e cu1 cu2 H) as [H1 | H1];
[left; exact H1 | right; rewrite H1; apply Bool.orb_true_r].
Qed.

Lemma has_element_insert1_new : forall l : Rlist, forall cu : cursor,
forall e : element_t, forall cu1 : cursor,
has_element (insert1 l cu cu1 e) cu1 = true.
intro l; induction l; simpl.
intros _ _ cu; rewrite <- beq_nat_refl;
apply Bool.orb_true_l.
intros cu e cu1.
case (beq_nat (fst a) cu); simpl.
rewrite <- beq_nat_refl;
apply Bool.orb_true_l.
rewrite (IHl cu e cu1); apply Bool.orb_true_r.
Qed.

Lemma WF_insert1 : forall l : Rlist, forall cu : cursor, forall e : element_t,
forall cun : cursor, cun > 0 -> has_element l cun = false ->
well_formed l -> well_formed (insert1 l cu cun e).
intro l; induction l; simpl.
intros _ _ cun H _.
split.
exact H.
auto.
intros cu e cun Hp Hse [Hfst [Hhe Hwf]];
apply Bool.orb_false_elim in Hse; destruct Hse as [Hse1 Hse2].
case (beq_nat (fst a) cu); simpl.
split.
exact Hp.
split.
apply Bool.orb_false_intro.
apply beq_nat_false in Hse1; apply Bool.not_true_is_false; intro H;
apply beq_nat_true in H; rewrite H in Hse1; apply Hse1; reflexivity.
exact Hse2.
split; [exact Hfst |
split; [exact Hhe | exact Hwf]].
split.
exact Hfst.
split.
apply Bool.not_true_is_false; intro H.
destruct (has_element_insert1 l cu e (fst a) cun H) as [HH | HH].
rewrite HH in Hse1; rewrite <- beq_nat_refl in Hse1;
apply Bool.diff_true_false; exact Hse1.
rewrite HH in Hhe; apply Bool.diff_true_false; exact Hhe.
apply (IHl cu e cun Hp Hse2 Hwf).
Qed.

Lemma insert1_length :
forall (l : Rlist), forall (cu cun: cursor),
forall (e : element_t),
length (insert1 l cu cun e) = S(length l).
intros l cu cun e; induction l; simpl.
reflexivity.
case (beq_nat (fst a) cu); simpl;
[|rewrite IHl];
reflexivity.
Qed.

Lemma insert1_position1_O :
forall l : Rlist, well_formed l ->
forall cu : cursor, forall e : element_t,
forall cun : cursor, 
forall n : nat, n > 0 ->
position1 l cun n > 0 ->
position1 (insert1 l 0 cu e) cun n = position1 l cun n.
intros l Hwf cu e cun; induction l; simpl.
intros n _ H; contradict H; apply gt_irrefl.
simpl in Hwf; destruct Hwf as [Hfst [_ Hwf]];
intros n Hn; case_eq (beq_nat (fst a) 0).
intro Heq; apply beq_nat_true in Heq; contradict Hfst;
rewrite Heq; apply gt_irrefl.
case_eq (beq_nat (fst a) cun); simpl;
intro Hbeq; rewrite Hbeq.
intros; reflexivity.
intros _; apply (IHl Hwf (S n) (gt_Sn_O n)).
Qed.

Lemma insert1_position1_inf :
forall l : Rlist, well_formed l ->
forall b cun : cursor,
forall cu : cursor, forall e : element_t,
forall n : nat, n > 0 ->
position1 l b n > 0 ->
position1 l cun n > 0 -> position1 l b n > position1 l cun n ->
position1 (insert1 l b cu e) cun n = position1 l cun n.
intros l Hwf b cun cu e; induction l; simpl.
intros n _ H; contradict H; apply gt_irrefl.
simpl in Hwf; destruct Hwf as [Hfst [_ Hwf]];
intros n Hn; case (beq_nat (fst a) b); simpl.
case (beq_nat (fst a) cun).
intros _ _ H; contradict H; apply gt_irrefl.
intros _ Hpos Hko; contradict Hko; apply le_not_gt;
apply (le_trans _ (S n) _ (le_n_Sn n)).
apply (has_element_position1 l _ _) in Hpos.
apply (position1_has_element l _ _ Hpos).
case (beq_nat (fst a) cun).
intros; reflexivity.
apply (IHl Hwf (S n) (gt_Sn_O n)).
Qed.

Lemma insert1_position1_sup :
forall l : Rlist, well_formed l ->
forall b cun : cursor,
forall cu : cursor, forall e : element_t,
forall n : nat, n > 0 ->
position1 l b n > 0 -> has_element l cu = false ->
position1 l cun n > 0 -> position1 l b n <= position1 l cun n ->
position1 (insert1 l b cu e) cun n = position1 l cun n + 1.
intros l Hwf b cun cu e; induction l; simpl.
intros n _ H; contradict H; apply gt_irrefl.
simpl in Hwf; destruct Hwf as [Hfst [_ Hwf]];
intros n Hn; case (beq_nat (fst a) b); simpl.
case_eq (beq_nat (fst a) cun); intro Hacun.
apply beq_nat_true in Hacun; rewrite Hacun.
case_eq (beq_nat cun cu);
[intros _ _ Hko; contradict Hko; rewrite Bool.orb_true_l;
apply Bool.diff_true_false|].
case_eq (beq_nat cu cun);
[intro Heq; apply beq_nat_true in Heq; rewrite Heq;
intro Hko; contradict Hko; rewrite <- beq_nat_refl;
apply Bool.diff_true_false|intros _ _ _ _ _ _].
rewrite <- plus_n_Sm; rewrite <- plus_n_O; reflexivity.
intros _; case_eq (beq_nat cu cun).
intros Hcucun Hko Hpos; apply beq_nat_true in Hcucun;
rewrite Hcucun in Hko; rewrite Hacun in Hko;
rewrite Bool.orb_false_l in Hko; contradict Hko.
rewrite (has_element_position1 _ _ _ Hpos).
apply Bool.diff_true_false.
intros _ _ Hpos _.
apply (has_element_position1 l _ _) in Hpos.
apply (plus_reg_l _ _ (S n)).
repeat (rewrite (plus_comm (S n))); rewrite <- (plus_assoc _ 1);
simpl; apply (position1_eq _ cun Hpos _ (S n)).
case (beq_nat (fst a) cun).
intros Hpos _ _ Hko; contradict Hko.
apply gt_not_le; apply le_S_gt.
apply (has_element_position1 l _ _ ) in Hpos.
apply (position1_has_element l _ _ Hpos).
intros Hpb Hhe; apply Bool.orb_false_elim in Hhe;
destruct Hhe as [_ Hhe].
apply (IHl Hwf _ (gt_Sn_O n) Hpb Hhe).
Qed.

Lemma insert1_element1_old :
forall l : Rlist, well_formed l ->
forall b cu : cursor, forall e : element_t,
forall cun : cursor, forall n : nat, n > 0 ->
has_element l cu = false ->
position1 l cun n > 0 ->
element1 l cun = element1 (insert1 l b cu e) cun.
intros l Hwf b cu e cun; induction l; simpl.
intros n _ _ Hko; contradict Hko; apply gt_irrefl.
simpl in Hwf; destruct Hwf as [Hfst [_ Hwf]];
case (beq_nat (fst a) b); simpl.
case_eq (beq_nat (fst a) cun); intro Hacun.
case_eq (beq_nat cu cun); intro Hcucun;
[apply beq_nat_true in Hcucun; rewrite <- Hcucun in Hacun;
rewrite Hacun; intros n _ Hko; rewrite Bool.orb_true_l in
Hko; contradict Hko; apply Bool.diff_true_false |
intros; reflexivity].
case_eq (beq_nat (fst a) cu); intro Hacu;
[apply beq_nat_true in Hacu; rewrite Hacu in Hacun;
rewrite Hacun; intros; reflexivity |].
case_eq (beq_nat cu cun); intro Hcucun;
[| intros; reflexivity].
apply beq_nat_true in Hcucun; rewrite Hcucun.
intros n _ Hko Hpos; rewrite Bool.orb_false_l in Hko; contradict Hko.
rewrite (has_element_position1 _ _ _ Hpos);
apply Bool.diff_true_false.
case (beq_nat (fst a) cun).
intros; reflexivity.
intros n _ Hhe; apply Bool.orb_false_elim in Hhe;
destruct Hhe as [_ Hhe].
apply (IHl Hwf _ (gt_Sn_O n) Hhe).
Qed.

Lemma insert1_position1_new_O :
forall l : Rlist, well_formed l ->
forall cu : cursor, forall e : element_t,
forall n : nat,
has_element l cu = false ->
position1 (insert1 l 0 cu e) cu n = length l + n.
intros l Hwf cu e; induction l; simpl.
intro n; rewrite <- beq_nat_refl; reflexivity.
simpl in Hwf; destruct Hwf as [Hfst [_ Hwf]];
case_eq (beq_nat (fst a) 0); simpl; intro HaO;
[apply beq_nat_true in HaO; rewrite HaO in Hfst;
contradict Hfst; apply gt_irrefl|].
case (beq_nat (fst a) cu);
[intros n Hko; contradict Hko; rewrite Bool.orb_true_l;
apply Bool.diff_true_false|].
rewrite Bool.orb_false_l;
intro n; rewrite plus_n_Sm; apply (IHl Hwf).
Qed.

Lemma insert1_position1_new :
forall l : Rlist, well_formed l ->
forall b cu : cursor, forall e : element_t,
forall n : nat,
has_element l cu = false ->
position1 l b n > 0 ->
position1 (insert1 l b cu e) cu n = position1 l b n.
intros l Hwf b cu e; induction l; simpl.
intros n _ Hko; contradict Hko; apply gt_irrefl.
simpl in Hwf; destruct Hwf as [Hfst [_ Hwf]];
case (beq_nat (fst a) b); simpl.
rewrite <- beq_nat_refl; intros; reflexivity.
case (beq_nat (fst a) cu);
[intros n Hko; contradict Hko; rewrite Bool.orb_true_l;
apply Bool.diff_true_false|].
rewrite Bool.orb_false_l;
intro n; apply (IHl Hwf).
Qed.

Lemma insert1_element1_new :
forall l : Rlist, well_formed l ->
forall b cu : cursor, forall e : element_t,
has_element l cu = false ->
element1 (insert1 l b cu e) cu = e.
intros l Hwf b cu e; induction l; simpl.
intros _; rewrite <- beq_nat_refl; reflexivity.
simpl in Hwf; destruct Hwf as [Hfst [_ Hwf]];
case (beq_nat (fst a) b); simpl.
rewrite <- beq_nat_refl; intros; reflexivity.
case (beq_nat (fst a) cu);
[intros Hko; contradict Hko; rewrite Bool.orb_true_l;
apply Bool.diff_true_false|].
rewrite Bool.orb_false_l; apply (IHl Hwf).
Qed.

Lemma equivalent_insert1 :
forall l li : Rlist, well_formed l -> well_formed li ->
forall b cu : cursor, forall e : element_t,
has_element li cu = true -> element1 li cu = e ->
has_element l cu = false ->
(forall cun : cursor,
has_element l cun = true ->
has_element li cun = true  /\ element1 li cun = element1 l cun) ->
length li = S(length l) ->
equivalent (insert1 l b cu e) li.
unfold equivalent; 
intros l li Hwfl Hwfli b cu e Hhellicu Hellicu Hhellcu Hhe Hlgth.
rewrite <- (insert1_length l b cu e) in Hlgth.
rewrite Hlgth.
split; [reflexivity | intros cun Hhelincun].
destruct (has_element_insert1 _ _ _ _ _ Hhelincun) as [Heq | Hhelcun].
rewrite <- Heq; split; [apply Hhellicu| rewrite Hellicu; 
apply (insert1_element1_new l Hwfl _ _  _ Hhellcu)].
destruct (Hhe cun Hhelcun) as [Hhelicun Hel].
split; [exact Hhelicun|].
rewrite Hel; symmetry; apply (insert1_element1_old _ Hwfl _ _ _ _ 1
(gt_Sn_O O)Hhellcu(position1_has_element _ _ _ Hhelcun)).
Qed.

(*** DELETE1 ***)

Fixpoint delete1 (l : Rlist) (cu : cursor) : Rlist :=
match l with
nil => nil
| a :: ls =>
if beq_nat (fst a) cu then ls else a :: (delete1 ls cu)
end.

Lemma delete1_has_element :
forall l : Rlist,
forall cu cun : cursor, well_formed l ->
has_element (delete1 l cu) cun = true ->
has_element l cun = true /\ cu <> cun.
intros l cu cun; induction l; simpl.
intros _ H; contradict H; apply Bool.diff_false_true.
case_eq (beq_nat (fst a) cu); simpl.
intros Heq [_[Hhela _]] H; apply beq_nat_true in Heq;
split; [rewrite H; apply Bool.orb_true_r|].
intro HH; contradict H; rewrite <- HH;
rewrite <- Heq; rewrite Hhela;
apply Bool.diff_false_true.
intros Hneq [_[_ Hwf]].
case_eq (beq_nat (fst a) cun).
split; [apply Bool.orb_true_l|].
intro Heq; contradict Hneq; rewrite Heq;
apply beq_nat_true in H; rewrite H;
rewrite <- beq_nat_refl; apply Bool.diff_true_false.
intros _; repeat (rewrite Bool.orb_false_l).
apply (IHl Hwf).
Qed.

Lemma delete1_has_element_inv :
forall l : Rlist, forall cu cun : cursor,
has_element l cun = true ->
has_element (delete1 l cu) cun = true \/ cu = cun.
intros l cu cun; induction l; simpl.
intro H; left; exact H.
case_eq (beq_nat (fst a) cu); simpl.
intro Hacu; apply beq_nat_true in Hacu; rewrite Hacu.
case_eq (beq_nat cu cun);
[intros Hcucun _; right; apply (beq_nat_true _ _ Hcucun)
|intros _ Hhe; rewrite Bool.orb_false_l in Hhe; left; exact Hhe].
case_eq (beq_nat (fst a) cun).
intros _ _ _; left; apply Bool.orb_true_l.
intros _ _ Hhe; rewrite Bool.orb_false_l in Hhe;
destruct (IHl Hhe) as [Hhd|Heq];
[rewrite Bool.orb_false_l; left; exact Hhd|right; exact Heq].
Qed.

Lemma WF_delete1 : forall l : Rlist, forall cu : cursor,
well_formed l -> well_formed (delete1 l cu).
intros l cu; induction l; simpl.
auto.
case (beq_nat (fst a) cu); simpl.
intros [_[_ H]]; exact H.
intros [Hfst[Hhe Hwf]];
case_eq(has_element (delete1 l cu) (fst a)).
intro HH; apply (delete1_has_element _ _ _ Hwf) in HH;
destruct HH as [Hhea _].
rewrite Hhea in Hhe;
contradict Hhe; apply Bool.diff_true_false.
split; [exact Hfst|split;
[reflexivity|apply IHl; exact Hwf]].
Qed.

Lemma delete1_length :
forall l : Rlist, forall cu : cursor, forall n : nat,
position1 l cu n > 0 -> length l = S(length(delete1 l cu)).
intros l cu; induction l; simpl.
intros _ H; contradict H; apply gt_irrefl.
intro n; case (beq_nat (fst a) cu); simpl.
intros _; reflexivity.
intro H; rewrite (IHl _ H); reflexivity.
Qed.

Lemma delete1_position1_deleted :
forall l : Rlist, well_formed l ->
forall cu : cursor,
forall n : nat,
position1 l cu n > 0 ->
position1 (delete1 l cu) cu n = 0.
intros l Hwf cu; induction l; simpl.
intros; reflexivity.
simpl in Hwf; destruct Hwf as [_[Hhe Hwf]];
intros n; case_eq (beq_nat (fst a) cu); intros Hacu Hn; simpl.
apply beq_nat_true in Hacu; rewrite <- Hacu.
destruct (gt_O_eq (position1 l (fst a) n)) as [Hhf|Hhf].
contradict Hhe;
rewrite (has_element_position1 l (fst a) n Hhf).
apply Bool.diff_true_false.
symmetry; exact Hhf.
rewrite Hacu.
apply (IHl Hwf (S n) Hn).
Qed.

Lemma delete1_position1_sup :
forall l : Rlist,
forall cu cun : cursor,
forall n : nat,
position1 l cu n > 0 ->
position1 l cun n > position1 l cu n ->
position1 l cun n = 1 + position1 (delete1 l cu) cun n.
intros l cu cun; induction l; simpl.
intros _ H; contradict H; apply gt_irrefl.
intro n; case(beq_nat (fst a) cu); simpl.
intro Hn; case (beq_nat (fst a) cun); simpl.
intro Hko; contradict Hko; apply gt_irrefl.
intro Hpos; apply (gt_trans _ _ _ Hpos) in Hn.
apply (has_element_position1 l _ _) in Hn.
apply (plus_reg_l _ _ n); repeat(rewrite(plus_comm n));
rewrite plus_Sn_m; rewrite plus_n_Sm.
apply (position1_eq l cun Hn (S n) n).
intro Hpos; case (beq_nat (fst a) cun); simpl.
apply (has_element_position1 l) in Hpos.
intro Hko; contradict Hko; apply le_not_gt.
apply (le_trans _ _ _ (le_n_Sn n)).
apply (position1_has_element l cu (S n) Hpos).
apply (IHl (S n) Hpos).
Qed.

Lemma delete1_position1_inf :
forall l : Rlist,
forall cu cun : cursor,
forall n : nat,
position1 l cu n > 0 ->
position1 l cu n > position1 l cun n ->
position1 (delete1 l cu) cun n = position1 l cun n.
intros l cu cun; induction l; simpl.
intros _ H; contradict H; apply gt_irrefl.
intro n; case(beq_nat (fst a) cu); simpl.
intro Hn; case (beq_nat (fst a) cun); simpl.
intro Hko; contradict Hko; apply gt_irrefl.
intro Hpos; destruct (gt_O_eq (position1 l cun (S n))) as [Hko|H].
apply (has_element_position1 l) in Hko.
contradict Hpos; apply le_not_gt.
apply (le_trans _ _ _ (le_n_Sn n)).
apply (position1_has_element l cun (S n) Hko).
rewrite <- H; clear H.
destruct (gt_O_eq (position1 l cun n)) as [Hko|H].
apply (has_element_position1 l) in Hko.
contradict Hpos; apply le_not_gt.
apply (le_trans _ _ _ (le_n_Sn n)).
apply (position1_has_element l cun (S n) Hko).
symmetry; exact H.
intro Hpos; case (beq_nat (fst a) cun); simpl.
intros; reflexivity.
apply (IHl (S n) Hpos).
Qed.

Lemma delete1_element1 :
forall l : Rlist,
forall cu cun : cursor, forall n : nat,
position1 l cu n > 0 ->
cun <> cu ->
element1 (delete1 l cu) cun = element1 l cun.
intros l cu cun; induction l; simpl.
intros _ Hko; contradict Hko; apply gt_irrefl.
intro n; case_eq (beq_nat (fst a) cu); intro Hacu; simpl.
intros Hn HH; apply beq_nat_true in Hacu; rewrite Hacu.
case_eq (beq_nat cu cun); intro Hccu;
[apply beq_nat_true in Hccu; contradict HH; symmetry; exact Hccu|
reflexivity].
case (beq_nat (fst a) cun).
intros; reflexivity.
apply IHl.
Qed.

Lemma equivalent_delete1 :
forall l ld : Rlist, well_formed l -> well_formed ld ->
forall cu : cursor,
has_element l cu = true -> has_element ld cu = false ->
(forall cun : cursor,
has_element l cun = true -> cun <> cu ->
has_element ld cun = true /\ element1 ld cun = element1 l cun) ->
length l = S(length ld) ->
equivalent (delete1 l cu) ld.
unfold equivalent; 
intros l led Hwfl Hwfld cu Hhellcu Hhelldcu Hhe Hlgth.
rewrite (delete1_length l cu 1
(position1_has_element _ _ _ Hhellcu)) in Hlgth.
apply eq_add_S in Hlgth; rewrite Hlgth.
split; [reflexivity | intros cun Hheldcun].
destruct (delete1_has_element _ cu _ Hwfl Hheldcun) as [Hhelcun Hd].
destruct (Hhe cun Hhelcun) as [Hheledcun Hel].
intro HH; contradict Hd; rewrite HH; reflexivity.
split; [exact Hheledcun|].
rewrite Hel; apply (delete1_element1 _ _ _ _
(position1_has_element _ _ _ Hhellcu)).
intro HH; contradict Hd; rewrite HH; reflexivity.
Qed.

(*** REPLACE1 ***)

Fixpoint replace1 (l : Rlist) (cu : cursor) (e : element_t) : Rlist :=
match l with
nil => nil
| a :: ls =>
if beq_nat (fst a) cu then (fst a,e) :: ls else a :: (replace1 ls cu e)
end.

Lemma replace1_has_element :
forall l : Rlist, forall cu : cursor, forall e : element_t,
forall cun : cursor,
has_element (replace1 l cu e) cun = true ->
has_element l cun = true.
intros l cu e cun; induction l; simpl.
intro H; exact H.
case (beq_nat (fst a) cu); simpl.
intro H; rewrite H; reflexivity.
intro H; apply Bool.orb_true_elim in H;
destruct H as [H|H].
rewrite H; apply Bool.orb_true_l.
apply IHl in H; rewrite H; apply Bool.orb_true_r.
Qed.

Lemma WF_replace1 :
forall l : Rlist, forall cu : cursor, forall e : element_t,
well_formed l -> well_formed (replace1 l cu e).
intros l cu e; induction l; simpl.
auto.
case(beq_nat (fst a) cu); simpl.
intro H; exact H.
intros [Hfst[Hhe Hwf]];
split; [exact Hfst|split;[|apply IHl; exact Hwf]].
case_eq(has_element(replace1 l cu e) (fst a)); intro Hre;
[rewrite <- Hhe; symmetry; apply (replace1_has_element l cu e); exact Hre
|reflexivity].
Qed.

Lemma replace1_length :
forall l : Rlist, forall cu : cursor, forall e : element_t,
length l = length(replace1 l cu e).
intros l cu e; induction l; simpl.
reflexivity.
case (beq_nat (fst a) cu); simpl; 
[|rewrite <- IHl]; reflexivity.
Qed.

Lemma replace1_element1_replaced :
forall l : Rlist, forall cu : cursor, forall e : element_t,
forall n : nat,
position1 l cu n > 0 -> element1 (replace1 l cu e) cu = e.
intros l cu e; induction l; simpl.
intros _ Hko; contradict Hko; apply gt_irrefl.
intro n; case_eq (beq_nat (fst a) cu); simpl;
intro Hacu; rewrite Hacu.
intros _; reflexivity.
apply IHl.
Qed.

Lemma replace1_position1 :
forall l : Rlist, forall cu : cursor, forall e : element_t,
forall cun : cursor, forall n : nat,
position1 (replace1 l cu e) cun n = position1 l cun n.
intros l cu e cun; induction l; simpl.
intros _; reflexivity.
intro n; case (beq_nat (fst a) cu); simpl.
reflexivity.
case (beq_nat (fst a) cun).
reflexivity.
apply IHl.
Qed.

Lemma replace1_element1 :
forall l : Rlist, forall cu : cursor, forall e : element_t,
forall cun : cursor,
cu <> cun ->
element1 (replace1 l cu e) cun = element1 l cun.
intros l cu e cun Hdiff; induction l; simpl.
reflexivity.
case_eq (beq_nat (fst a) cu); simpl; intro Hacu.
apply beq_nat_true in Hacu; rewrite Hacu;
case_eq(beq_nat cu cun); intro Hko;
[contradict Hdiff; apply beq_nat_true in Hko;
exact Hko|reflexivity].
case (beq_nat (fst a) cun).
reflexivity.
apply IHl.
Qed.

Lemma equivalent_replace1 :
forall l li : Rlist, well_formed l -> well_formed li ->
forall cu : cursor, forall e : element_t,
has_element l cu = true -> element1 li cu = e ->
(forall cun : cursor,
has_element l cun = true ->
has_element li cun = true  /\
(cu <> cun -> element1 li cun = element1 l cun)) ->
length li = length l ->
equivalent (replace1 l cu e) li.
unfold equivalent; 
intros l li Hwfl Hwfli cu e Hhelcu Hellicu Hhe Hlgth.
rewrite (replace1_length l cu e) in Hlgth.
rewrite Hlgth.
split; [reflexivity | intros cun Hhelrcun].
apply (replace1_has_element l) in Hhelrcun;
destruct (Hhe cun Hhelrcun) as [Hhelicun Hel].
split; [exact Hhelicun|case_eq (beq_nat cu cun)].
intro Heq; apply beq_nat_true in Heq; rewrite <- Heq;
rewrite Hellicu; apply (replace1_element1_replaced _ _ _ 1);
apply (position1_has_element l cu 1 Hhelcu).
intro Hdiff; apply beq_nat_false in Hdiff;
rewrite (Hel Hdiff); apply (replace1_element1); exact Hdiff.
Qed.

(*** LIST ***)

Record list := {this :> Rlist; wf : well_formed this}.

(*** EMPTY ***)

Lemma WF_nil : well_formed nil.
simpl.
auto.
Qed.

Definition empty : list :=
Build_list List.nil WF_nil.

(*** POSITION ***)

Definition position (l : list) (cu : cursor) : nat :=
position1 l cu 1.

Lemma position_has_element :
forall l : list, forall n : cursor,
has_element l n = true -> position l n > 0.
intros l n HH; unfold position.
apply (position1_has_element l n 1 HH).
Qed.

Lemma has_element_position:
forall l : list, forall n : cursor,
position l n > 0 -> has_element l n = true.
intros l n HH; unfold position.
apply (has_element_position1 l n 1 HH).
Qed.

Lemma position_no_element :
forall l:list, position l 0 = 0.
unfold position; intro l.
apply (position1_no_element l (wf l)).
apply gt_Sn_O.
Qed.

Lemma position_eq :
  (forall (co:list),
   (forall (cu1:cursor),
    (forall (cu2:cursor),
     ((position co cu1) > 0 ->
      ((position co cu1) = (position co cu2) -> cu1 = cu2))))).
intros [l Hwf] cu1 cu2.
unfold position; simpl.
intros Hp Heq.
assert (1 > 0).
apply gt_Sn_O.
rewrite <- (position1_nth l Hwf cu1 1
(has_element_position1 l cu1 1 Hp) H).
rewrite Heq.
rewrite Heq in Hp.
rewrite (position1_nth l Hwf cu2 1
(has_element_position1 l cu2 1 Hp) H).
reflexivity.
Qed.

(*** LENGTH ***)

Definition length (l : list) : nat := List.length (this l).

Lemma position_length :
forall (l : list), forall (cu : cursor),
position l cu <= length l.
unfold position.
intros l cu.
apply lt_n_Sm_le.
rewrite (plus_n_O (length l)).
rewrite plus_n_Sm.
apply position1_length.
apply gt_Sn_O.
Qed.

Lemma length_position :
forall l : list,
(forall cu : cursor, position l cu = 0) -> length l = 0.
intros [l H]; unfold position; unfold length; simpl;
 case l; simpl.
intros; reflexivity.
clear l H; intros a l H.
remember (H (fst a)) as Hko; clear HeqHko.
rewrite <- beq_nat_refl in Hko.
symmetry in Hko; contradict Hko.
apply O_S.
Qed.

(*** PREVIOUS ***)

Definition previous (l : list) (cu : cursor) : cursor :=
previous1 (this l) cu 0.

Lemma position_previous_gen :
forall (l : list), forall (cu:cursor),
position l cu  > 1 ->
position l (previous l cu) = position l cu - 1.
unfold position; unfold previous; simpl;
intros l cu Hpos.
assert (cu > 0).
apply lt_le_weak in Hpos;
destruct (gt_O_eq cu) as [H | H];
[exact H | contradict Hpos; rewrite <- H];
rewrite (position1_no_element l (wf l) 1 (gt_Sn_O 0));
apply gt_not_le; apply gt_Sn_O.
apply gt_pred in Hpos; rewrite pred_of_minus in Hpos.
assert(0 < position1 l cu 1 - 1).
exact (lt_S_n 0 (position1 l cu 1 - 1)
(le_lt_n_Sm 1 (position1 l cu 1 - 1)
(gt_le_S 0 (position1 l cu 1 - 1) Hpos))).
assert(has_element l cu = true).
apply has_element_position1 with 1.
apply le_gt_trans with (position1 l cu 1 - 1).
rewrite <- pred_of_minus; apply le_pred_n.
exact Hpos.
rewrite (previous1_nth l (wf l) cu H ((position1 l cu 1) - 1) 0 Hpos).
rewrite (nth_position1 l (wf l) (position1 l cu 1 - 1 - 1) 1).
rewrite <- pred_of_minus; rewrite <- plus_n_Sm;
rewrite <- plus_n_O;
rewrite <- (S_pred (position1 l cu 1 - 1) 0 H0); reflexivity.
rewrite <- pred_of_minus.
apply lt_S_n; apply le_lt_n_Sm.
rewrite <- (S_pred (position1 l cu 1 - 1) 0 H0).
rewrite plus_n_O with (List.length (this l)).
apply le_trans with (position1 l cu 1);
[rewrite <- pred_of_minus; apply le_pred_n|
apply le_S_n; rewrite plus_n_Sm].
apply position1_length; apply gt_Sn_O.
symmetry; apply (position1_nth l (wf l) cu 1 H1); apply gt_Sn_O.
Qed.

Lemma position_previous_first :
forall (l : list), forall (cu : cursor),
position l cu = 1 -> previous l cu = 0.
intros [l H] cu; unfold position; unfold previous;simpl;
case l; simpl;
[ intros Hko; contradict Hko; apply O_S |].
clear l H; intros a l; case_eq (beq_nat (fst a) cu);
intro H; simpl;
[auto| intro Hko; contradict Hko].
case_eq (has_element l cu);
intro Ht; intro HH.
apply (position1_has_element l cu 2) in Ht;
simpl in Ht.
rewrite HH in Ht.
contradict Ht; apply gt_not_le; apply gt_Sn_n.
generalize Ht; apply Bool.eq_true_false_abs.
apply (has_element_position1 l) with 2;
simpl; rewrite HH; apply gt_Sn_n.
Qed.

Lemma previous_O :
forall (l : list),
previous l 0 = 0.
intros l.
unfold previous; simpl; apply previous1_O; apply (wf l).
Qed.

(*** NEXT ***)

Definition next (l : list) (cu : cursor) : cursor :=
next1 (this l) cu.

Lemma next_position_gen :
forall l : list, forall cu : cursor,
length l > position l cu -> position l cu > 0 ->
position l (next l cu) = position l cu + 1.
unfold position; unfold length; intros [l H] cu Hl Hpos; simpl.
rewrite <- (position1_nth l H cu 1
(has_element_position1 l cu 1 Hpos) (gt_Sn_O 0)) at 1.
unfold next; simpl;
rewrite next1_nth with l (fst (nth (position1 l cu 1 - 1) l (0, e_nl)))
(position1 l cu 1 - 1); [| exact H | reflexivity].
rewrite <- pred_of_minus.
rewrite <- (S_pred (position1 l cu 1) 0 Hpos).
rewrite (nth_position1 l H (position1 l cu 1) 1); [reflexivity|].
auto.
Qed.

Lemma next_position_last :
forall l : list, forall cu : cursor,
position l cu = length l -> next l cu = 0.
unfold position; unfold length; unfold next; intros [l Hwf]; simpl.
case_eq l; [simpl; intros; reflexivity|].
intros a ll Hal cu; rewrite <- Hal; intro H.
assert (position1 l cu 1 > 0).
rewrite H; rewrite Hal; simpl;
apply gt_Sn_O.
rewrite <- (position1_nth l Hwf cu 1); simpl;
[|apply (has_element_position1 l cu 1) |];
[|simpl; exact H0|apply gt_Sn_O].
rewrite <- pred_of_minus.
rewrite (next1_nth l Hwf
(fst (nth (pred (position1 l cu 1)) l (0, e_nl)))
(pred(position1 l cu 1))).
rewrite <- (S_pred (position1 l cu 1) 0 H0).
rewrite (nth_overflow l (0, e_nl)); simpl;
[reflexivity | rewrite H; apply le_refl].
reflexivity.
Qed.

Lemma next_position_O :
forall (l : list), next l 0 = 0.
unfold next; intros [l H]; simpl; induction l; simpl.
reflexivity.
simpl in H; destruct H as [Hfst [_ H]].
case_eq (beq_nat (fst a) 0); intro HH.
apply beq_nat_true in HH; contradict Hfst; rewrite HH;
apply gt_irrefl.
apply IHl; exact H.
Qed.

Lemma next_has_element_inv :
forall l : list,
forall cu : cursor,
position l (next l cu) > 0 ->
position l cu > 0 /\ length l > position l cu.
intros [l H] cu; unfold position; unfold length;
unfold next; simpl; intro Hpos;
destruct (next1_has_element_inv l H cu 1 (gt_Sn_O O) Hpos)
as [ Hpcu Hlength ].
split; [exact Hpcu | rewrite (plus_comm _ 1) in Hlength;
apply plus_gt_reg_l in Hlength; exact Hlength].
Qed.

(*** FIRST ***)

Definition first (l : list) : cursor :=
first1 (this l).

Lemma position_first_gen :
forall l : list,
length l <> 0 -> position l (first l) = 1.
intros [l H]; unfold length; unfold position;
unfold first; simpl; case l; simpl.
intro Hko; contradict Hko; reflexivity.
clear; intros a l _; rewrite <- beq_nat_refl; reflexivity.
Qed.

Lemma first_nil :
forall l : list,
length l = 0 -> first l = 0.
intros [l H]; unfold length;
unfold first; simpl; case l; simpl.
intros; reflexivity.
clear; intros a l Hko; symmetry in Hko; contradict Hko;
apply O_S.
Qed.

(*** LAST ***)

Definition last (l : list) : cursor :=
last1 (this l).

Lemma position_last_gen :
forall l : list,
position l (last l) = length l.
intros [l H]; unfold last; unfold length; unfold position; simpl.
apply position1_last1; exact H.
Qed.

Lemma last_nil :
forall l : list, length l = 0 -> last l = 0.
intros [l Hwf]; unfold last; unfold length; simpl.
rewrite last1_nth; case l; simpl.
intros; reflexivity.
intros p lp H; contradict H; intro HH;
apply gt_irrefl with 0; rewrite <- HH at 1;
apply gt_Sn_O.
Qed.

(*** ELEMENT ***)

Definition element (l : list) (cu : cursor) : element_t :=
element1 l cu.

(*** FIND ***)

Lemma find_position :
forall l : list, forall e : witness_t,
position l (find l e) = 0 -> find l e = 0.
intros l e; unfold position; apply find_position1.
apply gt_Sn_O.
Qed.

Lemma find_element :
forall l : list, forall e : witness_t,
position l (find l e) > 0 ->
eq_witness (witness(element l (find l e))) e.
intros l e; unfold position; unfold element; apply find_element1.
apply gt_Sn_O.
exact (wf l).
Qed.

Lemma find_element_rev :
forall l : list, forall cu : cursor,
position l cu > 0 ->
position l (find l (witness(element l cu))) > 0.
intros l e; unfold position; unfold element; apply find_element1_rev.
apply gt_Sn_O.
Qed.

Lemma find_is_first_gen :
forall l : list,
forall e : witness_t, forall cun : cursor,
position l (find l e) > position l cun ->
position l cun > 0 ->
not (eq_witness (witness(element1 l cun)) e).
intros l e cun; unfold position; unfold element; apply find_is_first1_gen.
apply gt_Sn_O.
Qed.

Lemma find_is_first_O :
forall l : list,
forall e : witness_t, forall cun : cursor,
position l (find l e) = 0 ->
position l cun > 0 -> not (eq_witness (witness(element l cun)) e).
intros l e cun; unfold position; unfold element; apply find_is_first1_O.
apply gt_Sn_O.
Qed.

Lemma find_nil :
forall l : list, forall e : witness_t,
length l = 0 -> find l e = 0.
intros [l Hwf] e; unfold length; simpl; case l; simpl; [reflexivity
|intros a ls H; symmetry in H; contradict H; apply O_S].
Qed.

(*** LEFT ***)

Definition left (s : list) (cu : cursor) : list :=
if beq_nat cu 0 then s
else Build_list (left1 s cu) (WF_left1 s (wf s) cu).

Lemma left_nil :
forall l : list, left l 0 = l.
intros l; unfold left; simpl.
reflexivity.
Qed.

Lemma left_length : 
forall (l : list), forall (cu : cursor),
position l cu > 0 -> length (left l cu) = position l cu - 1.
intros [l H] cu; unfold position; unfold left; simpl.
case_eq (beq_nat cu 0); [intro Hko | intros _].
apply beq_nat_true in Hko; rewrite Hko at 1.
intro HH;
rewrite (position1_no_element l H 1 (gt_Sn_O 0)) in HH.
contradict HH; apply gt_irrefl.
unfold length; simpl.
apply (left1_length l cu 1 (gt_Sn_O 0)).
Qed.

Lemma left_position_out :
forall (l : list), forall (cu : cursor),
position l cu > 0 ->
forall (cun : cursor), position l cu <= position l cun ->
position (left l cu) cun = 0.
intros [l Hwf] cu; unfold position; unfold left; simpl.
case_eq (beq_nat cu 0); [intro Hko | intros _].
apply beq_nat_true in Hko; rewrite Hko at 1.
intro HH;
rewrite (position1_no_element l Hwf 1 (gt_Sn_O 0)) in HH.
contradict HH; apply gt_irrefl.
simpl; apply (left1_position1_out l cu 1 (gt_Sn_O 0)).
Qed.

Lemma left_position_in :
forall (l : list), forall (cu : cursor),
position l cu > 0 ->
forall (cun : cursor), position l cu > position l cun ->
position (left l cu) cun = position l cun.
intros [l Hwf] cu; unfold position; unfold left; simpl.
case_eq (beq_nat cu 0); [intro Hko | intros _].
apply beq_nat_true in Hko; rewrite Hko at 1.
intro HH;
rewrite (position1_no_element l Hwf 1 (gt_Sn_O 0)) in HH.
contradict HH; apply gt_irrefl.
simpl; apply (left1_position1_in l cu 1 (gt_Sn_O 0)).
Qed.

Lemma left_element_in :
forall (l : list), forall (cu : cursor),
position l cu > 0 ->
forall (cun : cursor), position l cu > position l cun ->
element (left l cu) cun = element l cun.
intros [l Hwf] cu; unfold position; unfold left;
unfold element; simpl.
case_eq (beq_nat cu 0); [intro Hko | intros _].
apply beq_nat_true in Hko; rewrite Hko at 1.
intro HH;
rewrite (position1_no_element l Hwf 1 (gt_Sn_O 0)) in HH.
contradict HH; apply gt_irrefl.
simpl; apply (left1_element1_in l cu 1 (gt_Sn_O 0)).
Qed.

Lemma left_position_inv :
forall (l : list), forall (cu : cursor),
position l cu > 0 ->
forall (cun : cursor), position (left l cu) cun > 0 ->
position l cun = position (left l cu) cun.
intros l cu Hpos cun Hlpos.
case_eq (leb (position l cu) (position l cun)); intro H.
apply leb_complete in H.
apply (left_position_out l cu Hpos) in H.
contradict Hlpos; rewrite H; apply gt_irrefl.
apply leb_complete_conv in H.
symmetry; apply (left_position_in l cu Hpos cun H).
Qed.

(*** RIGHT ***)

Definition right (s : list) (cu : cursor) : list :=
if beq_nat cu 0 then empty
else Build_list (right1 s cu) (WF_right1 s (wf s) cu).

Lemma right_nil :
forall l : list, right l 0 = empty.
intros l; unfold right; simpl.
reflexivity.
Qed.

Lemma right_length : 
forall (l : list), forall (cu : cursor),
position l cu > 0 ->
length (right l cu) = length l - position l cu + 1.
intros [l H] cu; unfold position; unfold right; simpl.
case_eq (beq_nat cu 0); [intro Hko | intros _].
apply beq_nat_true in Hko; rewrite Hko at 1.
intro HH;
rewrite (position1_no_element l H 1 (gt_Sn_O 0)) in HH.
contradict HH; apply gt_irrefl.
unfold length; simpl; intro HH.
rewrite (right1_length l cu 1 (gt_Sn_O 0) HH).
rewrite <- plus_n_Sm; rewrite <- plus_n_Sm.
rewrite <- plus_n_O; rewrite <- plus_n_O.
symmetry; apply minus_Sn_m.
generalize (position_length (Build_list l H) cu);
intro Hp; unfold position in Hp; unfold length in Hp;
simpl in Hp; exact Hp.
Qed.

Lemma right_position_out :
forall (l : list), forall (cu : cursor),
position l cu > 0 ->
forall (cun : cursor), position l cu > position l cun ->
position (right l cu) cun = 0.
intros [l Hwf] cu; unfold position; unfold right; simpl.
case_eq (beq_nat cu 0); [intro Hko | intros _].
apply beq_nat_true in Hko; rewrite Hko at 1.
intro HH;
rewrite (position1_no_element l Hwf 1 (gt_Sn_O 0)) in HH.
contradict HH; apply gt_irrefl.
simpl; apply (right1_position1_out l Hwf cu 1 (gt_Sn_O 0)).
Qed.

Lemma right_position_in :
forall (l : list), forall (cu : cursor),
position l cu > 0 ->
forall (cun : cursor), position l cu <= position l cun ->
position (right l cu) cun = position l cun - position l cu + 1.
intros [l Hwf] cu; unfold position; unfold right; simpl.
case_eq (beq_nat cu 0); [intro Hko | intros _].
apply beq_nat_true in Hko; rewrite Hko at 1.
intro HH;
rewrite (position1_no_element l Hwf 1 (gt_Sn_O 0)) in HH.
contradict HH; apply gt_irrefl.
intros Hp cun Hs; simpl.
apply (plus_reg_l _ _ (position1 l cu 1)).
rewrite plus_assoc.
rewrite <- (le_plus_minus _ _ Hs).
rewrite plus_comm.
apply (right1_position1_in l cu 1 (gt_Sn_O 0) Hp cun Hs).
Qed.

Lemma right_element_in :
forall (l : list), forall (cu : cursor),
position l cu > 0 ->
forall (cun : cursor), position l cu <= position l cun ->
element (right l cu) cun = element l cun.
intros [l Hwf] cu; unfold position; unfold right;
unfold element; simpl.
case_eq (beq_nat cu 0); [intro Hko | intros _].
apply beq_nat_true in Hko; rewrite Hko at 1.
intro HH;
rewrite (position1_no_element l Hwf 1 (gt_Sn_O 0)) in HH.
contradict HH; apply gt_irrefl.
simpl; apply (right1_element1_in l cu 1 (gt_Sn_O 0)).
Qed.

Lemma right_position_inv :
forall (l : list), forall (cu : cursor),
position l cu > 0 ->
forall (cun : cursor), position (right l cu) cun > 0 ->
position l cun = position (right l cu) cun + position l cu -1.
intros l cu Hpos cun Hlpos.
case_eq (leb (position l cu) (position l cun)); intro H.
apply leb_complete in H.
rewrite (right_position_in l cu Hpos cun H).
rewrite <- (plus_n_Sm (position l cun - position l cu) 0).
rewrite <- plus_n_O; rewrite plus_Sn_m;
rewrite <- pred_of_minus; rewrite <- pred_Sn.
rewrite plus_comm; apply le_plus_minus;
exact H.
apply leb_complete_conv in H.
apply (right_position_out l cu Hpos) in H.
contradict Hlpos; rewrite H; apply gt_irrefl.
Qed.

Lemma has_element_right :
forall (l : list), forall (cu cun : cursor),
position (right l cu) cun > 0 ->
position l cun > 0.
intros [l H] cu cun; unfold position; unfold right; simpl.
case (beq_nat cu 0); simpl.
intro Hko; contradict Hko; apply gt_irrefl.
intro Hpos;
apply (has_element_position1) in Hpos.
apply has_element_right1 in Hpos.
apply (position1_has_element _ _ _ Hpos).
Qed.

(*** INSERT ***)

Lemma WF_insert : forall l : Rlist, forall cu : cursor,
forall e : element_t,
well_formed l -> well_formed (insert1 l cu (New_Max.new l) e).
intros l cu e H; apply WF_insert1.
apply New_Max.new_valid.
apply New_Max.new_has_element.
exact H.
Qed.

Definition insert (s : list) (cu : cursor) (e : element_t) : list :=
Build_list (insert1 s cu (New_Max.new s) e) (WF_insert s cu e (wf s)).

Lemma insert_length :
forall (l : list), forall (cu : cursor),
forall (e : element_t),
length (insert l cu e) = length l + 1.
intros [l H] cu; unfold length; unfold insert; simpl.
rewrite <- plus_n_Sm; rewrite <- plus_n_O; apply insert1_length.
Qed.

Lemma insert_position_O :
forall l : list, forall e : element_t, forall cun : cursor,
position l cun > 0 ->
position (insert l 0 e) cun = position l cun.
intros [l H] e cun; unfold position; unfold length; simpl.
apply (insert1_position1_O l H (New_Max.new l) e cun 1 (gt_Sn_O O)).
Qed.

Lemma insert_position_inf :
forall l : list,
forall b cun : cursor, forall e : element_t,
position l b > 0 ->
position l cun > 0 -> position l b > position l cun ->
position (insert l b e) cun = position l cun.
intros [l Hwf] b cun e; unfold insert;
unfold position; simpl.
apply (insert1_position1_inf l Hwf b cun (New_Max.new l) e 1 (gt_Sn_O O)).
Qed.

Lemma insert_position_sup :
forall l : list,
forall b cun : cursor, forall e : element_t,
position l b > 0 ->
position l b <= position l cun ->
position (insert l b e) cun = position l cun + 1.
intros [l Hwf] b cun e; unfold insert;
unfold position; simpl.
intros H1 H2;
apply (insert1_position1_sup l Hwf b cun (New_Max.new l) e 1 (gt_Sn_O O) H1
(New_Max.new_has_element l) (le_gt_trans _ _ _ H2 H1) H2).
Qed.

Lemma insert_element_old :
forall l : list, forall b : cursor,
forall e : element_t, forall cun : cursor,
position l cun > 0 -> element l cun = element (insert l b e) cun.
intros [l H] b e cun; unfold position; unfold element; simpl.
apply (insert1_element1_old l H b (New_Max.new l) e cun 1 (gt_Sn_O O)).
apply (New_Max.new_has_element).
Qed.

Lemma insert_position_new_O :
forall l : list,
forall e : element_t,
position (insert l O e) (New_Max.new l) = length l + 1.
intros [l H] e; unfold position; unfold insert;
unfold length; simpl.
apply (insert1_position1_new_O _ H).
apply (New_Max.new_has_element).
Qed.

Lemma insert_position_new :
forall l : list, forall b : cursor,
forall e : element_t,
position l b > 0 ->
position (insert l b e) (New_Max.new l) = position l b.
intros [l H] b e; unfold position; unfold insert;
unfold length; simpl.
apply (insert1_position1_new _ H).
apply (New_Max.new_has_element).
Qed.

Lemma insert_position_rev_new :
forall l : list, forall b : cursor,
forall e : element_t, forall cun : cursor,
position (insert l b e) cun = position (insert l b e) (New_Max.new l) ->
position l cun = 0.
intros l b e cun Heq; symmetry in Heq;
apply position_eq in Heq; unfold position.
destruct (gt_O_eq (position1 l cun 1)) as [H|H];
[|symmetry; exact H].
apply (has_element_position1) in H.
contradict H; rewrite <- Heq; rewrite New_Max.new_has_element;
apply Bool.diff_false_true.
apply le_S_gt.
apply (position1_has_element (insert l b e) _ _
(has_element_insert1_new _ _ _ _)).
Qed.

Lemma insert_element_new :
forall l : list, forall b : cursor,
forall e : element_t, forall cun : cursor,
position (insert l b e) cun = position (insert l b e) (New_Max.new l) ->
element (insert l b e) cun = e.
intros l b e cun Heq; symmetry in Heq;
apply position_eq in Heq;
unfold insert; unfold element; unfold position; simpl.
rewrite <- Heq; apply (insert1_element1_new _ (wf l));
apply (New_Max.new_has_element).
apply (position1_has_element (insert l b e) _ _
(has_element_insert1_new _ _ _ _)).
Qed.

Lemma insert_has_element :
forall l : list, forall b : cursor,
forall e : element_t, forall cun : cursor,
position (insert l b e) cun > 0 ->
cun = New_Max.new l \/ position l cun > 0.
intros [l H] b e cun; unfold position; unfold insert; simpl.
intro Hpos;
apply (has_element_position1 (insert1 l b (New_Max.new l) e) _ 1) in Hpos.
apply has_element_insert1 in Hpos.
destruct Hpos as [Heq|Hhe]; [left|right].
symmetry; exact Heq.
apply (position1_has_element _ _ _ Hhe).
Qed.

Lemma insert_has_element_rev :
forall l : list, forall b : cursor,
forall e : element_t, forall cun : cursor,
position l cun > 0 ->
position (insert l b e) cun > 0.
intros [l H] b e cun; unfold position; unfold insert; simpl.
intro Hpos;
apply (has_element_position1 l _ 1) in Hpos.
apply (insert1_has_element l b e cun (New_Max.new l)) in Hpos;
apply (position1_has_element _ _ _ Hpos).
Qed.

Lemma insert_has_element_new :
forall l : list, forall b : cursor,
forall e : element_t,
position (insert l b e) (New_Max.new l) > 0.
intros [l H] b e; unfold position; unfold insert; simpl.
apply (position1_has_element).
apply has_element_insert1_new.
Qed.

(*** DELETE ***)

Definition delete (s : list) (cu : cursor) : list :=
Build_list (delete1 s cu) (WF_delete1 s cu (wf s)).

Lemma delete_length :
forall l : list, forall cu : cursor,
position l cu > 0 -> length l =  1 + length(delete l cu).
intros [l H] cu; unfold position; unfold length; simpl.
apply delete1_length.
Qed.

Lemma delete_position_deleted :
forall l : list,
forall cu : cursor,
position l cu > 0 -> position (delete l cu) cu = 0.
intros [l H] cu; unfold position; unfold delete; simpl.
apply (delete1_position1_deleted l H).
Qed.

Lemma delete_position_sup :
forall l : list,
forall cu cun : cursor,
position l cu > 0 ->
position l cun > position l cu ->
position l cun = 1 + position (delete l cu) cun.
intros [l H] cu cun; unfold position; unfold delete; simpl.
apply (delete1_position1_sup l).
Qed.

Lemma delete_position_inf :
forall l : list,
forall cu cun : cursor,
position l cu > 0 ->
position l cu > position l cun ->
position (delete l cu) cun = position l cun.
intros [l H] cu cun; unfold position; unfold delete; simpl.
apply (delete1_position1_inf l).
Qed.

Lemma delete_element :
forall l : list,
forall cu cun : cursor,
position l cu > 0 ->
cun <> cu ->
element (delete l cu) cun = element l cun.
intros [l H] cu cun; unfold position; unfold delete; simpl.
apply (delete1_element1 l).
Qed.

(*** REPLACE ***)

Definition replace (s : list) (cu : cursor) (e : element_t) : list :=
Build_list (replace1 s cu e) (WF_replace1 s cu e (wf s)).

Lemma replace_length :
forall l : list, forall cu : cursor, forall e : element_t,
length l = length(replace l cu e).
intros [l H] cu e; unfold length; unfold replace; simpl;
apply replace1_length.
Qed.

Lemma replace_element_replaced :
forall l : list, forall cu : cursor, forall e : element_t,
position l cu > 0 -> element (replace l cu e) cu = e.
intros [l H] cu e; unfold position; unfold element; simpl;
apply replace1_element1_replaced.
Qed.

Lemma replace_position :
forall l : list, forall cu : cursor, forall e : element_t,
forall cun : cursor,
position (replace l cu e) cun = position l cun.
intros [l H] cu e cun; unfold position; unfold replace; simpl;
apply replace1_position1.
Qed.

Lemma replace_element :
forall l : list, forall cu : cursor, forall e : element_t,
forall cun : cursor,
cu <> cun ->
element (replace l cu e) cun = element l cun.
intros [l H] cu e cun; unfold element; unfold replace; simpl;
apply replace1_element1.
Qed.

(*** MAX ***)

Module Type CompareType.

Parameter Inline compare : element_t -> element_t -> Z.

Axiom compare_refl :
forall e : element_t, (compare e e = 0)%Z.

Axiom compare_asym :
forall e1 : element_t, forall e2 : element_t,
(0 <= compare e1 e2 <-> compare e2 e1 <= 0)%Z.

Axiom compare_trans :
forall e1 : element_t, forall e2 : element_t, forall e3 : element_t,
(compare e1 e2 <= 0)%Z -> (compare e2 e3 <= 0)%Z ->
(compare e1 e3 <= 0)%Z.

End CompareType.

Module Max (C : CompareType).

Fixpoint max2 (l : Rlist) (e : element_t) (r : cursor) : cursor :=
match l with
nil => r
| a :: ls => if (Zle_bool (0%Z) (C.compare e (snd a))) then
max2 ls e r else max2 ls (snd a) (fst a)
end.

Definition max (l : Rlist) : cursor :=
match l with
nil => 0
| a :: ls => max2 ls (snd a) (fst a)
end.

Lemma max2_has_element :
forall l : Rlist,
forall e : element_t, forall cu : cursor,
has_element l (max2 l e cu) = true \/ cu = max2 l e cu.
intros l; induction l; simpl.
intros _ cu; right; reflexivity.
intros e cu;
case(Zle_bool 0 (C.compare e (snd a))); simpl.
destruct (IHl e cu) as [Hhe | Heq].
left; rewrite Hhe; apply Bool.orb_true_r.
right; exact Heq.
destruct (IHl (snd a) (fst a)) as [Hhe | Heq].
left; rewrite Hhe; apply Bool.orb_true_r.
left; rewrite Heq at 1; rewrite <- beq_nat_refl;
apply Bool.orb_true_l.
Qed.

Lemma max_has_element :
forall l : Rlist,
List.length l <> 0 -> has_element l (max l) = true.
intros l; case l; clear l; simpl.
intros Hko; contradict Hko; reflexivity.
intros a l _;
destruct (max2_has_element l (snd a) (fst a)) as [Hhe|Heq].
rewrite Hhe; apply Bool.orb_true_r.
rewrite Heq at 1; rewrite <- beq_nat_refl;
apply Bool.orb_true_l.
Qed.

Lemma max2_base :
forall l : Rlist, well_formed l ->
forall em : element_t, forall cum : cursor,
has_element l cum = false ->
max2 l em cum = cum \/
(C.compare em (element1 l (max2 l em cum)) <= 0)%Z.
induction l; simpl.
intros; left; reflexivity.
intros [Hfst[Hha Hwf]] em cum Hint; apply Bool.orb_false_elim in Hint;
destruct Hint as [Hacum Hhcum]; apply beq_nat_false in Hacum.
case_eq (Zle_bool 0 (C.compare em (snd a))).
destruct (IHl Hwf em cum Hhcum) as [Hl | Hr].
intros _; left; exact Hl.
case_eq (beq_nat (fst a) (max2 l em cum)).
intro Hko; apply beq_nat_true in Hko; rewrite Hko in Hacum;
rewrite Hko in Hha; destruct (max2_has_element l em cum) as [H|H].
contradict H; rewrite Hha; apply Bool.diff_false_true.
contradict Hacum; symmetry; exact H.
intros; right; exact Hr.
intro Zint;
destruct(Zle_bool_total 0 (C.compare em (snd a))) as [Hko | HZle];
[|clear Zint; apply Zle_bool_imp_le in HZle].
contradict Hko; rewrite Zint; apply Bool.diff_false_true.
case_eq (beq_nat (fst a) (max2 l (snd a) (fst a))).
intros _; right; exact HZle.
destruct (IHl Hwf (snd a) _ Hha) as [Hko|Hres].
rewrite Hko; rewrite <- beq_nat_refl; intro H;
contradict H; apply Bool.diff_true_false.
intros _; right; apply (C.compare_trans _ _ _ HZle Hres).
Qed.

Lemma max2_base_inf :
forall l : Rlist, forall cu : cursor, well_formed l ->
forall em : element_t, forall cum : cursor,
has_element l cu = true ->
has_element l cum = false ->
max2 l em cum = cum ->
(C.compare (element1 l cu) em <= 0)%Z.
intros l cu; induction l; simpl.
intros _ em cum Hko; contradict Hko; apply Bool.diff_false_true.
case_eq (beq_nat (fst a) cu).
intros Heqacu [_[Hhea Hwf]] em cum;
case_eq (Zle_bool 0 (C.compare em (snd a))).
intros HZle _ _ _; apply Zle_bool_imp_le in HZle.
destruct (C.compare_asym em (snd a)) as [HH _].
apply (HH HZle).
intros _ _ Hint Hko.
apply Bool.orb_false_elim in Hint; destruct Hint as [Heqacum Hhecum].
destruct (max2_has_element l (snd a) (fst a)).
contradict H; rewrite Hko; rewrite Hhecum; apply Bool.diff_false_true.
apply beq_nat_false in Heqacum; contradict Heqacum;
rewrite H; apply Hko.
intros _ [Hfst[Hhea Hwf]] em cum;
case_eq (Zle_bool 0 (C.compare em (snd a))).
intros _ Hhecu Hint; rewrite Bool.orb_false_l in Hhecu;
apply Bool.orb_false_elim in Hint; destruct Hint as [_ Hhecun].
apply (IHl Hwf _ _ Hhecu Hhecun).
intros _ _ Hint Hko.
apply Bool.orb_false_elim in Hint; destruct Hint as [Heqacum Hhecum].
destruct (max2_has_element l (snd a) (fst a)).
contradict H; rewrite Hko; rewrite Hhecum; apply Bool.diff_false_true.
apply beq_nat_false in Heqacum; contradict Heqacum;
rewrite H; apply Hko.
Qed.

Lemma max2_element1 :
forall cu : cursor,
forall l : Rlist, well_formed l ->
forall em : element_t, forall cum : cursor,
has_element l cum = false ->
has_element l cu = true -> max2 l em cum = cum \/
(C.compare (element1 l cu) (element1 l (max2 l em cum)) <= 0)%Z.
intros cu l; induction l; simpl.
intros _ _ cum _ Hko; contradict Hko; apply Bool.diff_false_true.
intros [Hfst[Hhe Hwf]] em cum Hint;
apply Bool.orb_false_elim in Hint; destruct Hint as [Hacum Hhecum];
apply beq_nat_false in Hacum.
case_eq (Zle_bool 0 (C.compare em (snd a))).
case_eq (beq_nat (fst a) (max2 l em cum)).
intros Hko; apply beq_nat_true in Hko;
destruct(max2_has_element l em cum) as [Hhel|Heq].
contradict Hhel; rewrite <- Hko; rewrite Hhe;
apply Bool.diff_false_true.
contradict Hacum; rewrite Heq; rewrite Hko; reflexivity.
case_eq(beq_nat (fst a) cu).
intros Hacu _ Hle _; apply Zle_bool_imp_le in Hle.
destruct (max2_base l Hwf em cum Hhecum) as [Heq |HZle].
left; exact Heq.
right; destruct (C.compare_asym em (snd a)) as [Ht _];
apply Ht in Hle.
apply (C.compare_trans _ _ _ Hle HZle).
intros _ _ _ Hhcu; rewrite Bool.orb_false_l in Hhcu;
apply (IHl Hwf em cum Hhecum Hhcu).
case_eq (beq_nat (fst a) (max2 l (snd a) (fst a))).
case_eq (beq_nat (fst a) cu).
intros; right; rewrite C.compare_refl; apply Zle_refl.
intros _ Heqamax Hzle Hhecu; rewrite Bool.orb_false_l in Hhecu;
apply beq_nat_true in Heqamax.
symmetry in Heqamax; right;
apply (max2_base_inf l cu Hwf _ _ Hhecu Hhe Heqamax).
case_eq (beq_nat (fst a) cu).
intros _ Hdiff _ _; right;
destruct (max2_base l Hwf (snd a) _ Hhe) as [Hko|Hres].
contradict Hdiff; rewrite Hko; rewrite <- beq_nat_refl;
apply Bool.diff_true_false.
exact Hres.
intros _ Hdiff _ Hhecu; right;
rewrite Bool.orb_false_l in Hhecu;
destruct (IHl Hwf (snd a) _ Hhe Hhecu) as [Hko|Hres].
contradict Hdiff; rewrite Hko; rewrite <- beq_nat_refl;
apply Bool.diff_true_false.
exact Hres.
Qed.

Lemma max_element :
forall cu : cursor,
forall l : list,
has_element l cu = true -> 
(C.compare (element l cu) (element l (max l)) <= 0)%Z.
unfold element;intros cu [l Hwf];
generalize Hwf; clear Hwf; case l; simpl.
intros _ Hko; contradict Hko; apply Bool.diff_false_true.
clear l; intros a l [_[Hhea Hwf]];
case_eq(beq_nat (fst a) (max2 l (snd a) (fst a)));
case (beq_nat (fst a) cu).
intros; rewrite C.compare_refl; apply Zle_refl.
intros Hamax Hhecu; apply beq_nat_true in Hamax;
rewrite Bool.orb_false_l in Hhecu; symmetry in Hamax;
apply (max2_base_inf l cu Hwf _ _ Hhecu Hhea Hamax).
intros Hdiff _; destruct (max2_base l Hwf (snd a) _ Hhea) as [Hko|Hres].
contradict Hdiff; rewrite Hko; rewrite <- beq_nat_refl;
apply Bool.diff_true_false.
exact Hres.
intros Hdiff Hhecu; rewrite Bool.orb_false_l in Hhecu;
destruct (max2_element1 cu l Hwf (snd a) _ Hhea Hhecu) as [Hko|Hres].
contradict Hdiff; rewrite Hko; rewrite <- beq_nat_refl;
apply Bool.diff_true_false.
exact Hres.
Qed.

End Max.

(*** SUM_OF ***)

Module Type WeightType.

Parameter Inline weight : element_t -> nat.

End WeightType.

Module Sum_Of (W : WeightType).

Fixpoint sum_of_weight (l : Rlist) : nat :=
match l with
nil => 0
| a :: ls => (W.weight (snd a)) + (sum_of_weight ls) 
end.

Lemma sum_of_delete1 :
forall l : Rlist,
forall cu : cursor,
has_element l cu = true ->
sum_of_weight l =
(W.weight (element1 l cu)) + sum_of_weight (delete1 l cu).
intros l; induction l; simpl.
intros _ Hko; contradict Hko; apply Bool.diff_false_true.
intro cu; case(beq_nat (fst a) cu).
intros; reflexivity.
intro Hhe; rewrite Bool.orb_false_l in Hhe; simpl;
rewrite (IHl cu Hhe).
rewrite plus_assoc; rewrite (plus_comm (W.weight (snd a)));
rewrite plus_assoc; reflexivity.
Qed.

Lemma sum_of_equivalent :
forall l1 l2 : Rlist, well_formed l1 -> well_formed l2 ->
equivalent l1 l2 -> sum_of_weight l1 = sum_of_weight l2.
unfold equivalent; induction l1; simpl.
intro l2; case l2; simpl; [reflexivity | intros a ll _ _ [Hko];
contradict Hko; apply O_S].
intros l2 [_[Hhel1a Hwf1]] Hwf2 [Hlgth Hcu];
generalize (Hcu (fst a)); rewrite <- beq_nat_refl.
rewrite Bool.orb_true_l; intros [Hhel2a Hell2a]; [reflexivity|].
symmetry in Hell2a;
rewrite (sum_of_delete1 l2 (fst a) Hhel2a).
rewrite Hell2a.
rewrite (IHl1 (delete1 l2 (fst a)) Hwf1 (WF_delete1 l2 (fst a) Hwf2));
[reflexivity|]; split.
apply eq_add_S.
rewrite <- (delete1_length l2 _ 1 (position1_has_element _ _ _ Hhel2a)).
rewrite Hlgth; reflexivity.
intros cu Hhel1cu; generalize (Hcu cu).
case_eq(beq_nat (fst a) cu); intro Heq.
apply beq_nat_true in Heq; rewrite <- Heq.
contradict Hhel1cu; rewrite <- Heq; rewrite Hhel1a;
apply Bool.diff_false_true.
rewrite Bool.orb_false_l; intro Hint; generalize (Hint Hhel1cu);
intros [Hhel2cu Helcu]; clear Hint.
destruct (delete1_has_element_inv _ (fst a) _ Hhel2cu) as [Hhedl2cu | Hko].
split; [exact Hhedl2cu|rewrite Helcu; symmetry;
apply (delete1_element1 _ _ _ _ (position1_has_element _ _ _ Hhel2a))].
intros Hko; contradict Heq; rewrite Hko;
rewrite <- beq_nat_refl; apply Bool.diff_true_false.
contradict Heq; rewrite Hko;
rewrite <- beq_nat_refl; apply Bool.diff_true_false.
Qed.

Lemma sum_of_delete :
forall l ld : list, forall cu : cursor,
has_element l cu = true -> has_element ld cu = false ->
(forall cun : cursor,
position l cun > 0 -> cun <> cu ->
position ld cun > 0 /\
element ld cun = element l cun) ->
length l = S(length ld) ->
sum_of_weight l =
(W.weight (element l cu)) + sum_of_weight ld.
intros [l Hwf] [ld Hwfd]; unfold position; unfold element; simpl.
intros cu Hhelcu Hheldcu Hpos Hlgth;
rewrite <- (sum_of_equivalent (delete1 l cu) ld (WF_delete1 l cu Hwf) Hwfd).
apply (sum_of_delete1 l cu Hhelcu).
apply (equivalent_delete1 l ld Hwf Hwfd cu Hhelcu Hheldcu);
[intros cun Hhelcun Hdiff|apply Hlgth].
apply (position1_has_element l cun 1) in Hhelcun; apply le_S_gt in Hhelcun.
destruct (Hpos cun Hhelcun Hdiff) as [Hhe Hel].
apply has_element_position1 in Hhe.
split; [exact Hhe|exact Hel].
Qed.

Lemma sum_of_replace1 :
forall l : Rlist,
forall cu : cursor, forall e : element_t,
has_element l cu = true ->
(W.weight (element1 l cu)) + sum_of_weight (replace1 l cu e)  =
(W.weight e) + sum_of_weight l.
intros l; induction l; simpl.
intros _ e Hko; contradict Hko; apply Bool.diff_false_true.
intros cu e; case(beq_nat (fst a) cu); simpl.
rewrite plus_assoc; rewrite (plus_comm  _ (W.weight e));
rewrite <- plus_assoc; reflexivity.
intro Hhe; rewrite plus_assoc; rewrite (plus_comm _ (W.weight (snd a))).
rewrite <- plus_assoc; rewrite (IHl cu e Hhe).
rewrite plus_assoc; rewrite (plus_comm (W.weight (snd a)));
rewrite plus_assoc; reflexivity.
Qed.

Lemma sum_of_replace :
forall l li : list,
forall cu : cursor, forall e : element_t,
has_element l cu = true ->
element li cu = e ->
(forall cun : cursor,
position l cun > 0 ->
position li cun > 0 /\
(cu <> cun -> element li cun = element l cun)) ->
length li = length l ->
(W.weight (element l cu)) + sum_of_weight li =
(W.weight e) + sum_of_weight l.
intros [l Hwf] [li Hwfi]; unfold position; unfold element;
unfold length; simpl; intros cu e Hhelcu Hellicu Hpos Hlgth.
rewrite <- (sum_of_equivalent (replace1 l cu e) li
(WF_replace1 l cu e Hwf) Hwfi).
apply (sum_of_replace1 l cu e Hhelcu).
apply (equivalent_replace1 l li Hwf Hwfi cu e Hhelcu Hellicu);
[intros cun Hhecun|exact Hlgth].
apply (position1_has_element _ _ 1) in Hhecun;
destruct (Hpos cun Hhecun) as [Hhelicun Hel].
split; [apply (has_element_position1 _ _ _ Hhelicun)|exact Hel].
Qed.

Lemma sum_of_insert1 :
forall l : Rlist,
forall b cu : cursor, forall e : element_t,
has_element l cu = false ->
sum_of_weight (insert1 l b cu e) = (W.weight e) + sum_of_weight l.
intros l; induction l; simpl.
reflexivity.
intros b cu e; case(beq_nat (fst a) b); simpl.
reflexivity.
intro Hhe; apply Bool.orb_false_elim in Hhe;
destruct Hhe as [_ Hhe].
rewrite (IHl b cu e Hhe).
rewrite plus_assoc; rewrite (plus_comm (W.weight (snd a)));
rewrite plus_assoc; reflexivity.
Qed.

Lemma sum_of_insert :
forall l li : list, forall i : nat,
forall cu : cursor, forall e : element_t,
has_element li cu = true -> has_element l cu = false ->
element li cu = e ->
(forall cun : cursor,
i <= position l cun ->
position li cun = S(position l cun) /\
element li cun = element l cun) ->
(forall cun : cursor,
has_element l cun = true ->
i > position l cun ->
position l cun = position li cun /\
element li cun = element l cun) ->
length li = S(length l) ->
sum_of_weight li =
(W.weight e) + sum_of_weight l.
intros [l Hwf] [li Hwfi]; unfold position; unfold element; simpl.
intros i cu e Hhelicu Hhelcu Hellicu Hsup Hinf Hlgth;
destruct (gt_O_eq cu) as [Hcu | Hko];
[|rewrite <- Hko in Hhelicu;
apply (position1_has_element _ _ 1) in Hhelicu;
contradict Hhelicu; rewrite (position1_no_element li Hwfi);
[apply le_Sn_n|apply gt_Sn_O]].
rewrite <- (sum_of_equivalent (insert1 l O cu e) li
(WF_insert1 l O e cu Hcu Hhelcu Hwf) Hwfi).
apply (sum_of_insert1 l O cu e Hhelcu).
apply (equivalent_insert1 l li Hwf Hwfi O cu e Hhelicu Hellicu Hhelcu);
[intros cun Hhelcun|apply Hlgth].
destruct (le_gt_dec i (position1 l cun 1)) as [Hpsup | Hpinf].
destruct (Hsup cun Hpsup) as [Hpos Hel].
generalize (gt_Sn_O (position1 l cun 1)); intro Hhelicun;
rewrite <- Hpos in Hhelicun;
apply (has_element_position1 _ _ _) in Hhelicun.
split; [exact Hhelicun|exact Hel].
destruct (Hinf cun Hhelcun Hpinf) as [Hpos Hel].
apply (position1_has_element _ _ 1) in Hhelcun.
rewrite Hpos in Hhelcun; apply has_element_position1 in Hhelcun.
split; [exact Hhelcun|exact Hel].
Qed.

Lemma sum_of_nil :
forall l : list, length l = 0 -> sum_of_weight l = 0.
unfold length; simpl; intros [l H]; induction l; simpl.
reflexivity.
intro Hko; symmetry in Hko; contradict Hko; apply O_S.
Qed.

Lemma sum_of_equal :
forall l1 l2 : list, 
(forall cu : cursor,
      position l1 cu = position l2 cu /\
      (position l1 cu > 0 ->
       element l1 cu = element l2 cu)) ->
sum_of_weight l1 = sum_of_weight l2.
unfold position; unfold element;
intros [l1 Hwf1] [l2 Hwf2]; simpl; intro Hcu.
apply (sum_of_equivalent l1 l2 Hwf1 Hwf2).
apply (equal_equivalent l1 l2 Hwf1 Hwf2 Hcu).
Qed.

Lemma sum_of_left1 :
forall l : Rlist, forall cu : cursor,
well_formed l ->
has_element l cu = true ->
sum_of_weight (left1 l (next1 l cu)) =
sum_of_weight (left1 l cu) + W.weight (element1 l cu).
intros l cu; induction l; simpl.
intros _ Hko; contradict Hko; apply Bool.diff_false_true.
case (beq_nat (fst a) cu); simpl.
case_eq l.
simpl; case_eq (beq_nat (fst a) 0);
[intros Heq _ [Hko _]; apply beq_nat_true in Heq;
contradict Hko; rewrite Heq; apply gt_irrefl|].
simpl; rewrite <- plus_n_O; reflexivity.
simpl; intros aa ll Hal [_[Hhe]];
case_eq (beq_nat (fst a) (fst aa));
[intro Hko; apply beq_nat_true in Hko; contradict Hhe;
rewrite Hko; rewrite <- beq_nat_refl; rewrite Bool.orb_true_l;
apply Bool.diff_true_false|].
rewrite <- beq_nat_refl; simpl; rewrite <- plus_n_O; reflexivity.
case_eq (beq_nat (fst a) (next1 l cu)); simpl.
intros Heq [Hfst[Hhefsta Hwf]] Hhe;
apply beq_nat_true in Heq;
destruct(next1_has_element_simpl l cu Hhe) as [Hko|Hko].
contradict Hko; rewrite <- Heq; rewrite Hhefsta;
apply Bool.diff_false_true.
contradict Hfst; rewrite Heq; rewrite Hko; apply gt_irrefl.
intros _ [_[_ Hwf]] Hhe; rewrite (IHl Hwf Hhe).
rewrite plus_assoc; reflexivity.
Qed.

Lemma sum_of_left :
forall l : list, forall cu : cursor,
has_element l cu = true ->
sum_of_weight (left l (next l cu)) =
sum_of_weight (left l cu) + W.weight (element l cu).
intros [l Hwf] cu; unfold left; unfold next;
unfold element; simpl.
case_eq (beq_nat cu 0); simpl.
intros Heq He; apply beq_nat_true in Heq;
rewrite Heq in He; apply (position1_has_element _ _ 1) in He;
contradict He; rewrite (position1_no_element l Hwf 1 (gt_Sn_O O));
apply le_Sn_n.
case_eq (beq_nat (next1 l cu) O); simpl.
intros Heq _; apply beq_nat_true in Heq;
rewrite <- (left1_O l Hwf) at 2;
rewrite <- Heq; apply (sum_of_left1 l cu Hwf).
intros _ _; apply (sum_of_left1 l cu Hwf).
Qed.

Lemma sum_of_right1 :
forall l : Rlist, forall cu : cursor,
well_formed l ->
has_element l cu = true ->
W.weight (element1 l cu) + sum_of_weight (right1 l (next1 l cu)) =
sum_of_weight (right1 l cu).
intros l cu; induction l; simpl.
intros _ Hko; contradict Hko; apply Bool.diff_false_true.
case (beq_nat (fst a) cu); simpl.
case_eq l.
simpl; case_eq (beq_nat (fst a) 0);
[intros Heq _ [Hko _]; apply beq_nat_true in Heq;
contradict Hko; rewrite Heq; apply gt_irrefl|].
simpl; rewrite <- plus_n_O; reflexivity.
simpl; intros aa ll Hal [_[Hhe]];
case_eq (beq_nat (fst a) (fst aa));
[intro Hko; apply beq_nat_true in Hko; contradict Hhe;
rewrite Hko; rewrite <- beq_nat_refl; rewrite Bool.orb_true_l;
apply Bool.diff_true_false|].
rewrite <- beq_nat_refl; simpl; reflexivity.
case_eq (beq_nat (fst a) (next1 l cu)); simpl.
intros Heq [Hfst[Hhefsta Hwf]] Hhe;
apply beq_nat_true in Heq;
destruct(next1_has_element_simpl l cu Hhe) as [Hko|Hko].
contradict Hko; rewrite <- Heq; rewrite Hhefsta;
apply Bool.diff_false_true.
contradict Hfst; rewrite Heq; rewrite Hko; apply gt_irrefl.
intros _ [_[_ Hwf]] Hhe; rewrite (IHl Hwf Hhe).
reflexivity.
Qed.

Lemma sum_of_right :
forall l : list, forall cu : cursor,
has_element l cu = true ->
W.weight (element l cu) + sum_of_weight (right l (next l cu)) =
sum_of_weight (right l cu).
intros [l Hwf] cu; unfold right; unfold next;
unfold element; simpl.
case_eq (beq_nat cu 0); simpl.
intros Heq He; apply beq_nat_true in Heq;
rewrite Heq in He; apply (position1_has_element _ _ 1) in He;
contradict He; rewrite (position1_no_element l Hwf 1 (gt_Sn_O O));
apply le_Sn_n.
case_eq (beq_nat (next1 l cu) O); simpl.
assert(0 = sum_of_weight nil); [simpl; reflexivity|];
intros Heq _; apply beq_nat_true in Heq;
rewrite H; rewrite <- (right1_O l Hwf);
rewrite <- Heq; apply (sum_of_right1 l cu Hwf).
intros _ _; apply (sum_of_right1 l cu Hwf).
Qed.

End Sum_Of.

End Raw_List.

