Require Import "list_raw".
Require Import Reals.
Require Import List.

Module Type ROrder.

Parameter Inline lt_real_bool : R -> R -> bool.

Parameter Inline le_real_bool : R -> R -> bool.

Parameter Inline gt_real_bool : R -> R -> bool.

Parameter Inline ge_real_bool : R -> R -> bool.

Parameter Inline eq_real_bool : R -> R -> bool.

Parameter Inline neq_real_bool : R -> R -> bool.

Axiom lt_real_bool_axiom :
  (forall (x:R), (forall (y:R), ((lt_real_bool x y) = true <-> (Rlt x y)))).

Axiom le_real_bool_axiom :
  (forall (x:R), (forall (y:R), ((le_real_bool x y) = true <-> (Rle x y)))).

Axiom gt_real_bool_axiom :
  (forall (x:R), (forall (y:R), ((gt_real_bool x y) = true <-> (Rgt x y)))).

Axiom ge_real_bool_axiom :
  (forall (x:R), (forall (y:R), ((ge_real_bool x y) = true <-> (Rge x y)))).

Axiom eq_real_bool_axiom :
  (forall (x:R), (forall (y:R), ((eq_real_bool x y) = true <-> (eq x y)))).

Axiom neq_real_bool_axiom :
  (forall (x:R), (forall (y:R), ((neq_real_bool x y) = true <-> ~(eq x y)))).

End ROrder.

Module Type ElementType.

Parameter Inline element_t : Set.

Parameter Inline e_nl : element_t.

Parameter Inline witness : element_t -> R.

End ElementType.

Module Raw_Set (X : ElementType) (O : ROrder).

Lemma beq_real_refl : forall e : R, O.eq_real_bool e e = true.
intro e.
destruct (O.eq_real_bool_axiom e e) as [_ Heq].
apply Heq; reflexivity.
Qed.

Lemma beq_real_true : forall e1 : R, forall e2 : R,
O.eq_real_bool e1 e2 = true -> e1 = e2.
intros e1 e2 Hb.
destruct (O.eq_real_bool_axiom e1 e2) as [Heq _].
apply Heq in Hb; exact Hb.
Qed.

Lemma beq_real_false : forall e1 : R, forall e2 : R,
O.eq_real_bool e1 e2 = false -> e1 <> e2.
intros e1 e2 Hb He.
destruct (O.eq_real_bool_axiom e1 e2) as [_ Heq].
apply Heq in He; rewrite He in Hb; contradict Hb;
apply Bool.diff_true_false.
Qed.

Lemma beq_real_sym : forall e1 : R, forall e2 : R,
O.eq_real_bool e1 e2 = O.eq_real_bool e2 e1.
intros e1 e2; case_eq (O.eq_real_bool e1 e2).
intro Heq; apply beq_real_true in Heq; rewrite Heq;
symmetry; apply beq_real_refl.
intro Hdiff; case_eq (O.eq_real_bool e2 e1).
intro Heq; contradict Hdiff; apply beq_real_true in Heq;
rewrite Heq; rewrite beq_real_refl; apply Bool.diff_true_false.
reflexivity.
Qed.

Lemma gtb_real_correct :
forall m n : R, Rgt m n -> O.gt_real_bool m n = true.
intros m n Hgt; destruct (O.gt_real_bool_axiom m n) as [_ H].
apply (H Hgt).
Qed.

Lemma gtb_real_complete :
forall m n : R, O.gt_real_bool m n = true -> Rgt m n.
intros m n Hgt; destruct (O.gt_real_bool_axiom m n) as [H _].
apply (H Hgt).
Qed.

Lemma gtb_real_correct_conv :
forall m n : R, Rle m n -> O.gt_real_bool m n = false.
intros m n Hgt; destruct (O.gt_real_bool_axiom m n) as [H _].
case_eq (O.gt_real_bool m n).
intros Hko; apply H in Hko; contradict Hko;
apply Rle_not_gt; exact Hgt.
reflexivity.
Qed.

Lemma gtb_real_complete_conv :
forall m n : R, O.gt_real_bool m n = false -> Rle m n.
intros m n Hgt; destruct (O.gt_real_bool_axiom m n) as [_ H].
apply Rnot_gt_le; intro HH; apply H in HH.
rewrite HH in Hgt; contradict Hgt; apply Bool.diff_true_false.
Qed.

Module E.

Definition element_t : Set := X.element_t.

Definition witness_t : Set := R.

Definition witness : element_t -> witness_t := X.witness.

Definition e_nl : element_t := X.e_nl.

Definition eq_witness (e1 : witness_t) (e2 : witness_t) : Prop :=
e1 = e2.

Definition beq_witness (e1 : witness_t) (e2 : witness_t) : bool :=
O.eq_real_bool e1 e2.

Lemma beq_witness_refl : forall e : witness_t, beq_witness e e = true.
apply beq_real_refl.
Qed.

Lemma beq_witness_true : forall e1 : witness_t, forall e2 : witness_t,
beq_witness e1 e2 = true -> eq_witness e1 e2.
apply beq_real_true.
Qed.

Lemma beq_witness_false : forall e1 : witness_t, forall e2 : witness_t,
beq_witness e1 e2 = false -> not (eq_witness e1 e2).
apply beq_real_false.
Qed.

End E.

Module Raw_List := list_raw.Raw_List(E).

Import Raw_List.
Import X.

(*** WELL_FORMED ***)

Fixpoint well_formed_hashed (l : Rlist) : Prop :=
match l with
nil => True
| a :: ls => find ls (witness (snd a)) = 0
/\ well_formed_hashed ls
end.

(*** MAP ***)

Record hset := {hthis :> list; hwf : well_formed_hashed hthis}.

(***** ADDITION TO LIST_RAW *****)

(*** FIND ***)

Lemma find_position1_inv :
forall l : Rlist, well_formed_hashed l -> well_formed l ->
forall cun : cursor, forall n : nat,  
position1 l cun n > 0 ->
position1 l (find l (witness (element1 l cun))) n
= position1 l cun n.
intros l Hmap Hwf cun;
induction l; simpl.
intros _ Hko; contradict Hko; apply gt_irrefl.
case_eq (beq_nat (fst a) cun); intro Hacun.
rewrite beq_real_refl.
rewrite <- beq_nat_refl.
intros; reflexivity.
simpl in Hmap.
simpl in Hwf; destruct Hwf as [Hfst[Hhe Hwf]];
intros n Hpos;
destruct Hmap as [Hfind Hmap].
assert(position1 l (find l (witness (snd a))) (S n) = 0).
rewrite Hfind; apply (position1_no_element l Hwf _ (gt_Sn_O n)).
apply (find_is_first1_O l (witness (snd a))
cun _ (gt_Sn_O n)) in H; [|exact Hpos].
case_eq(O.eq_real_bool (witness (snd a))
          (witness (element1 l cun))).
intro Heq; apply beq_real_true in Heq.
contradict H; symmetry; exact Heq.
intros _;
case_eq (beq_nat (fst a) (find l (witness (element1 l cun)))).
intro Hko; apply beq_nat_true in Hko.
destruct (gt_O_eq
(position1 l (find l (witness (element1 l cun))) (S n)))
as [Hpl|Hpl].
rewrite <- Hko in Hpl;
apply (has_element_position1 l _ _) in Hpl.
contradict Hhe; rewrite Hpl; apply Bool.diff_true_false.
symmetry in Hpl; apply (find_position1 _ _ _ (gt_Sn_O n)) in Hpl.
contradict Hfst; rewrite Hko; rewrite Hpl; 
apply gt_irrefl.
intros _; apply (IHl Hmap Hwf _ Hpos).
Qed.

Lemma find_position_inv :
forall l : list, well_formed_hashed l ->
forall cun : cursor,
position l cun > 0 ->
position l (find l (witness (element l cun)))
= position l cun.
intros [l H]; unfold position; unfold element; simpl;
intros Hh cun; apply (find_position1_inv l Hh H cun).
Qed.

Lemma find_O_diff :
forall l : list, forall cu : cursor, forall w : R,
find l w = 0 ->
position l cu > 0 ->
witness(element l cu) <> w.
intros l cu w Hw Hpos; apply (find_is_first1_O _ _ _ 1 (gt_Sn_O O));
unfold position in Hpos.
rewrite Hw; apply position1_no_element;
[exact (wf l)|apply gt_Sn_O].
exact Hpos.
Qed.

(*** INSERT ***)

Lemma insert1_find :
forall l : Rlist, forall w : R,
forall b cu : cursor, forall e : element_t,
w <> witness e -> find l w = find (insert1 l b cu e) w.
intros l w b cu e Hw; induction l; simpl.
case_eq (O.eq_real_bool (witness e) w);
[intro Heq; apply beq_real_true in Heq;
contradict Hw; rewrite Heq|]; reflexivity.
case (beq_nat (fst a) b); simpl.
case_eq (O.eq_real_bool (witness e) w);
[intro Heq; apply beq_real_true in Heq;
contradict Hw; rewrite Heq|]; reflexivity.
case(O.eq_real_bool (witness (snd a)) w).
reflexivity.
exact IHl.
Qed.

Lemma insert_find :
forall l : list, forall w : R,
forall b : cursor, forall e : element_t,
w <> witness e ->
find l w = find (insert l b e) w.
intros [l Hwf] w b e; unfold insert; simpl.
apply insert1_find.
Qed.

Lemma insert1_find_new :
forall l : Rlist,
forall b cu : cursor, forall e : element_t,
well_formed l -> find l (witness e) = 0 ->
find (insert1 l b cu e) (witness e) = cu.
intros l b cu e; induction l; simpl.
rewrite beq_real_refl; reflexivity.
case (beq_nat (fst a) b); simpl.
rewrite beq_real_refl;
case (O.eq_real_bool (witness (snd a)) (witness e)); simpl;
reflexivity.
case (O.eq_real_bool (witness (snd a)) (witness e)); simpl.
intros [Hko _] Heq; contradict Hko; rewrite Heq; apply gt_irrefl.
intros [_[_]]; apply IHl.
Qed.

Lemma insert_find_new :
forall l : list,
forall b : cursor, forall e : element_t,
find l (witness e) = 0 ->
find (insert l b e) (witness e) = New_Max.new l.
intros [l Hwf] b e; unfold insert; simpl.
apply (insert1_find_new l _ _ _ Hwf).
Qed.

(*** DELETE ***)

Lemma WFh_delete1 :
forall l : Rlist, forall cu : cursor,
well_formed l ->
well_formed_hashed l -> well_formed_hashed (delete1 l cu).
intros l cu; induction l; simpl.
auto.
intros [Hfst[Hhe Hwf]];
case (beq_nat (fst a) cu); simpl.
intros [_ H]; exact H.
intros [Hf Hwfh]; split; [|apply (IHl Hwf Hwfh)].
generalize Hf Hwf; clear; induction l; simpl.
reflexivity.
case_eq (O.eq_real_bool (witness (snd a0)) (witness (snd a))).
intros _ He [Hko _]; contradict Hko; rewrite He; apply gt_irrefl.
case (beq_nat (fst a0) cu); simpl.
intros _ He _; exact He.
intros Heq Hf [_[_ Hwf]]; rewrite Heq.
apply (IHl Hf Hwf).
Qed.

Lemma delete1_find :
forall l : Rlist, forall w : R, forall cu : cursor,
has_element l cu = true ->
w <> witness(element1 l cu) ->
find (delete1 l cu) w = find l w.
intros l w cu; induction l; simpl.
reflexivity.
case_eq (beq_nat (fst a) cu); simpl.
case_eq (O.eq_real_bool (witness (snd a)) w); simpl.
intros Heq _ _ Hko; contradict Hko; apply beq_real_true in Heq;
rewrite Heq; reflexivity.
reflexivity.
case_eq (O.eq_real_bool (witness(snd a)) w); simpl.
reflexivity.
intros _ _; apply IHl.
Qed.

Lemma delete_find :
forall l : list, forall w : R, forall cu : cursor,
has_element l cu = true ->
w <> witness(element l cu) ->
find (delete l cu) w = find l w.
intros [l Hwf] w cu; unfold delete; unfold element; simpl.
apply delete1_find.
Qed.

Lemma delete1_find_deleted :
forall l : Rlist, forall cu : cursor,
has_element l cu = true -> 
well_formed l -> well_formed_hashed l ->
find (delete1 l cu) (witness(element1 l cu)) = O.
intros l cu; induction l; simpl.
reflexivity.
case (beq_nat (fst a) cu); simpl.
intros _ _ [Hfind _]; exact Hfind.
case_eq (O.eq_real_bool (witness (snd a)) (witness (element1 l cu))).
intros Heq Hhecu [_[_ Hwf]] [Hfind Hh]; apply beq_real_true in Heq;
contradict Hfind; rewrite Heq; intro HHfind.
apply (position1_has_element _ _ 1) in Hhecu; generalize Hhecu.
rewrite <- (find_position1_inv l Hh Hwf cu 1 Hhecu).
rewrite HHfind; rewrite (position1_no_element _ Hwf _ (gt_Sn_n O));
apply le_Sn_n.
intros _ Hhecu [_[_ Hwf]] [_ Hh]; exact (IHl Hhecu Hwf Hh).
Qed.

Lemma delete_find_deleted :
forall l : list, forall cu : cursor,
has_element l cu = true -> well_formed_hashed l ->
find (delete l cu) (witness(element l cu)) = O.
intros [l H] cu; unfold delete; unfold element; simpl.
intros Hhecu Ho; apply (delete1_find_deleted l _ Hhecu H Ho).
Qed.

(*** REPLACE ***)

Lemma replace1_find :
forall l : Rlist, forall w : R, forall e : element_t,
well_formed l -> w <> witness(e) ->
find (replace1 l (find l (witness e)) e) w = find l w.
intros l w e; induction l; simpl.
reflexivity.
case_eq (O.eq_real_bool (witness (snd a)) (witness e)); simpl.
rewrite <- beq_nat_refl.
case_eq (O.eq_real_bool (witness (snd a)) w); simpl.
intros Heq1 Heq2 _ Hko; contradict Hko; apply beq_real_true in Heq1;
apply beq_real_true in Heq2; rewrite <- Heq1; exact Heq2.
case_eq (O.eq_real_bool (witness e) w); simpl.
intros Heq _ _ _ Hko; contradict Hko; apply beq_real_true in Heq;
rewrite <- Heq; reflexivity.
reflexivity.
case_eq (beq_nat (fst a) (find l (witness e))); simpl.
intros Heq _ [Hfst[Hhe _]]; apply beq_nat_true in Heq;
destruct (find_has_element l (witness e)) as [Hko|Hko].
contradict Hhe; rewrite Heq; rewrite Hko; apply Bool.diff_true_false.
contradict Hfst; rewrite Heq; rewrite Hko; apply gt_irrefl.
case_eq (O.eq_real_bool (witness(snd a)) w); simpl.
reflexivity.
intros _ _ _ [_[_ Hwf]]; apply (IHl Hwf).
Qed.

Lemma replace_find :
forall l : list, forall w : R, forall e : element_t,
w <> witness(e) ->
find (replace l (find l (witness e)) e) w = find l w.
intros [l Hwf] w e; unfold replace;
unfold element; simpl.
apply (replace1_find _ _ _ Hwf).
Qed.

Lemma replace1_find_eq :
forall l : Rlist, forall e : element_t,
well_formed l -> 
find (replace1 l (find l (witness e)) e) (witness e) =
find l (witness e).
intros l e; induction l; simpl.
reflexivity.
case_eq (O.eq_real_bool (witness (snd a)) (witness e)); simpl.
rewrite <- beq_nat_refl; simpl; rewrite beq_real_refl; reflexivity.
case_eq (beq_nat (fst a) (find l (witness e))); simpl.
intros Heq _ [Hfst[Hhe _]]; apply beq_nat_true in Heq;
destruct (find_has_element l (witness e)) as [Hko|Hko].
contradict Hhe; rewrite Heq; rewrite Hko; apply Bool.diff_true_false.
contradict Hfst; rewrite Heq; rewrite Hko; apply gt_irrefl.
intros _ Heq [_[_ Hwf]]; rewrite Heq; apply (IHl Hwf).
Qed.

(*** LEFT_FIND ***)

Lemma left1_find_in :
forall l : Rlist, well_formed l ->
forall cu : cursor, forall w : R,
forall n : nat,
position1 l cu n > 0 ->
position1 l cu n > position1 l (find l w) n ->
find l w = find (left1 l cu) w.
intros l Hwf cu w; induction l; simpl.
reflexivity.
simpl in Hwf; destruct Hwf as [Hfst[Hhe Hwf]].
case (beq_nat (fst a) cu); simpl;
case (O.eq_real_bool (witness (snd a)) w); simpl.
rewrite <- beq_nat_refl; intros n _ Hko;
contradict Hko; apply gt_irrefl.
case (beq_nat (fst a) (find l w)).
intros n _ Hko; contradict Hko; apply gt_irrefl.
intros n _ Hko; apply (find_position1 l w (S n) (gt_Sn_O n)).
destruct (gt_O_eq (position1 l (find l w) (S n))) as [Hpos | HH];
[contradict Hko; apply le_not_gt|symmetry; exact HH].
apply (has_element_position1 l _ _) in Hpos.
apply (position1_has_element l _ (S n)) in Hpos.
apply (le_trans _ _ _ (le_n_Sn n) Hpos).
intros; reflexivity.
case_eq (beq_nat (fst a) (find l w)).
intro Hko; apply beq_nat_true in Hko;
destruct (find_has_element l w) as [Hf|Hf];
rewrite <- Hko in Hf.
rewrite Hf in Hhe; contradict Hhe; apply Bool.diff_true_false.
contradict Hfst; rewrite Hf; apply gt_irrefl.
intros _ n; apply (IHl Hwf).
Qed.

Lemma left1_find_out :
forall l : Rlist, well_formed l ->
forall cu : cursor, forall w : R,
forall n : nat,
position1 l cu n > 0 ->
position1 l cu n <= position1 l (find l w) n ->
find (left1 l cu) w = 0.
intros l Hwf cu w; induction l; simpl.
reflexivity.
simpl in Hwf; destruct Hwf as [Hfst[Hhe Hwf]].
case (beq_nat (fst a) cu); simpl; [reflexivity|].
case (O.eq_real_bool (witness (snd a)) w); simpl.
rewrite <- beq_nat_refl;
intros n Hpos Hko; contradict Hko; apply gt_not_le.
apply (has_element_position1 l _ _) in Hpos.
apply (position1_has_element l _ (S n)) in Hpos.
apply (le_gt_trans _ _ _ Hpos (gt_Sn_n n)).
case (beq_nat (fst a) (find l w)).
intros n Hpos Hko; contradict Hko; apply gt_not_le.
apply (has_element_position1 l _ _ ) in Hpos.
apply (position1_has_element l _ (S n)) in Hpos.
apply (le_gt_trans _ _ _ Hpos (gt_Sn_n n)).
intros n; apply (IHl Hwf).
Qed.

Lemma left_find_in :
forall l : list, forall cu : cursor, forall w : R,
position l cu > 0 ->
position l cu > position l (find l w) ->
find l w = find (left l cu) w.
intros [l H] cu w; unfold position; unfold left; simpl.
case (beq_nat cu 0); simpl.
reflexivity.
apply (left1_find_in l H _ _ _).
Qed.

Lemma left_find_out :
forall l : list, forall cu : cursor, forall w : R,
position l cu > 0 ->
position l cu <= position l (find l w) ->
find (left l cu) w = 0.
intros [l H] cu w; unfold position; unfold left; simpl.
case_eq (beq_nat cu 0); simpl.
intros Heq Hko; apply beq_nat_true in Heq; rewrite Heq in Hko;
rewrite (position1_no_element _ H _ (gt_Sn_O O)) in Hko.
contradict Hko; apply gt_irrefl.
intros _; apply (left1_find_out l H _ _ _).
Qed.

Lemma left_find_rev :
forall l : list, forall cu : cursor, forall w : R,
position l cu > 0 ->
position (left l cu) (find (left l cu) w) > 0 ->
find l w = find (left l cu) w.
intros l cu w.
case_eq (leb (position l cu) (position l (find l w))).
intros Hinf Hpos Hpfind; apply leb_complete in Hinf.
apply (left_find_out l cu w Hpos) in Hinf.
rewrite Hinf in Hpfind; rewrite (position_no_element) in Hpfind.
apply gt_irrefl in Hpfind; elim Hpfind.
intros Hsup Hpos Hpfind; apply leb_complete_conv in Hsup.
apply lt_not_le in Hsup; apply not_le in Hsup.
apply (left_find_in l cu w Hpos Hsup).
Qed.

(*** RIGHT_FIND ***)

Lemma right1_find_out :
forall l : Rlist, well_formed l -> well_formed_hashed l ->
forall cu : cursor, forall w : R,
forall n : nat,
position1 l cu n > 0 ->
position1 l cu n > position1 l (find l w) n ->
find (right1 l cu) w = 0.
intros l Hwf Hmap cu w; induction l; simpl.
reflexivity.
simpl in Hmap; destruct Hmap as [Hfind Hmap];
simpl in Hwf; destruct Hwf as [Hfst[Hhe Hwf]].
case (beq_nat (fst a) cu); simpl;
case_eq (O.eq_real_bool (witness (snd a)) w); simpl.
rewrite <- beq_nat_refl.
intros _ n _ Hko; contradict Hko; apply gt_irrefl.
case (beq_nat (fst a) (find l w)).
intros _ n _ Hko; contradict Hko; apply gt_irrefl.
intros _ n Hn Hinf; 
destruct (gt_O_eq (position1 l (find l w) (S n))) as [Hpos | HO].
contradict Hinf; apply le_not_gt.
apply (has_element_position1 l) in Hpos.
apply (position1_has_element l _ (S n)) in Hpos.
apply (le_trans _ _ _ (le_n_Sn n) Hpos).
symmetry in HO; apply (find_position1 l w (S n) (gt_Sn_O n) HO).
rewrite <- beq_nat_refl.
intros Hw n _ _; apply beq_real_true in Hw; rewrite <- Hw.
generalize Hfind Hwf; clear; induction l; simpl.
reflexivity.
case (beq_nat (fst a0) cu); simpl.
intros H _; exact H.
case (O.eq_real_bool (witness (snd a0)) (witness (snd a))).
intros Heq [Hko[_ _]]; contradict Hko; rewrite Heq; apply gt_irrefl.
intros Hf [_[_ Hwf]]; apply (IHl Hf Hwf).
intros _ n; case_eq (beq_nat (fst a) (find l w)).
intro Heq; apply beq_nat_true in Heq;
destruct (find_has_element l w) as [Hko|Hko].
rewrite <- Heq in Hko; rewrite Hhe in Hko; contradict Hko;
apply Bool.diff_false_true.
rewrite <- Heq in Hko; rewrite Hko in Hfst; contradict Hfst;
apply gt_irrefl.
intros _; apply (IHl Hwf Hmap).
Qed.

Lemma right_find_out :
forall l : list, well_formed_hashed l ->
forall cu : cursor, forall w : R,
position l cu > 0 ->
position l cu > position l (find l w) ->
find (right l cu) w = 0.
intros [l H] Hmap cu w; unfold position; unfold right; simpl.
case (beq_nat cu 0); simpl.
reflexivity.
apply (right1_find_out l H Hmap _ _ _).
Qed.

Lemma right1_find_in :
forall l : Rlist,
forall cu : cursor, forall w : R,
forall n : nat,
position1 l cu n > 0 ->
position1 l cu n <= position1 l (find l w) n ->
find l w = find (right1 l cu) w.
intros l cu w; induction l; simpl.
reflexivity.
case (beq_nat (fst a) cu); simpl; [reflexivity|].
case (O.eq_real_bool (witness (snd a)) w); simpl.
rewrite <- beq_nat_refl.
intros n Hpos Hko; contradict Hko; apply gt_not_le.
apply (has_element_position1 l _ _) in Hpos.
apply (position1_has_element l _ (S n)) in Hpos.
apply (le_gt_trans _ _ _ Hpos (gt_Sn_n n)).
case (beq_nat (fst a) (find l w)).
intros n Hpos Hko; contradict Hko; apply gt_not_le.
apply (has_element_position1 l _ _) in Hpos.
apply (position1_has_element l _ (S n)) in Hpos.
apply (le_gt_trans _ _ _ Hpos (gt_Sn_n n)).
intro n; apply (IHl).
Qed.

Lemma right_find_in :
forall l : list, forall cu : cursor, forall w : R,
position l cu > 0 ->
position l cu <= position l (find l w) ->
find l w = find (right l cu) w.
intros [l H] cu w; unfold position; unfold find; unfold right;
unfold first; simpl.
case_eq (beq_nat cu 0); simpl.
intro Heq; apply beq_nat_true in Heq; rewrite Heq.
intro Hko; rewrite (position1_no_element l H _ (gt_Sn_O O)) in Hko.
contradict Hko; apply gt_irrefl.
intros _; apply (right1_find_in l).
Qed.

Lemma right_find_rev :
forall l : hset,
forall cu : cursor, forall w : R,
position l cu > 0 ->
position (right l cu) (find (right l cu) w) > 0 ->
find l w = find (right l cu) w.
intros [l Hmap] cu w; simpl.
case_eq (leb (position l cu) (position l (find l w))).
intros Hinf Hpos Hpfind; apply leb_complete in Hinf.
apply (right_find_in l cu w Hpos Hinf).
intros Hsup Hpos Hpfind; apply leb_complete_conv in Hsup.
apply lt_not_le in Hsup; apply not_le in Hsup.
apply (right_find_out l Hmap cu w Hpos) in Hsup.
rewrite Hsup in Hpfind; rewrite (position_no_element) in Hpfind.
apply gt_irrefl in Hpfind; elim Hpfind.
Qed.

(*** EQUIVALENT ***)

Lemma equivalent_find :
forall m1 : hset, forall m2 : hset, forall w : R,
(forall i : R,
     has_element m1 (find m1 i) = true ->
     has_element m2 (find m2 i) = true) ->
length m1 = length m2 ->
has_element m2 (find m2 w) = true ->
has_element m1 (find m1 w) = true.
intros [[l1 Hwf1]Hh1] [[l2 Hwf2]Hh2] w; unfold length;
simpl; simpl in Hh1; simpl in Hh2;
generalize l1 l2 w Hh1 Hh2 Hwf1 Hwf2; clear.
intros l1; induction l1; simpl.
intro l2; case l2; simpl.
intros _ _ _ _ _ _ _ Hko; exact Hko.
intros a ll w _ _ _ _ _ Hko; contradict Hko; apply O_S.
intros l2 w [Hfind1 Hwfh1] Hwfh2 [Hfst[Hne Hwf1]] Hwf2 Himp Hlgth Hhe2;
case_eq (O.eq_real_bool (witness (snd a)) w).
intros _; rewrite <- beq_nat_refl; apply Bool.orb_true_l.
case (beq_nat (fst a) (find l1 w)).
intros _; apply Bool.orb_true_l.
intro Heqaw; rewrite Bool.orb_false_l.
apply beq_real_false in Heqaw.
generalize (delete1_has_element_inv _ (find l2 (witness (snd a))) _ Hhe2).
generalize (Himp (witness (snd a))).
rewrite beq_real_refl.
rewrite <- (beq_nat_refl (fst a)); rewrite Bool.orb_true_l.
intros Hint; assert (true = true). reflexivity.
apply Hint in H; clear Hint.
intros [Hhd | Heq]; [|contradict Heqaw;
rewrite <- (find_element1 l2 w 1 (gt_Sn_O O) Hwf2
(position1_has_element l2 _ _ Hhe2)); rewrite <- Heq;
rewrite (find_element1 l2 (witness (snd a)) 1 (gt_Sn_O O) Hwf2
(position1_has_element l2 _ _ H)); reflexivity].
rewrite (delete1_length l2 _ _ (position1_has_element l2 _ _ H))
in Hlgth; simpl in Hlgth; apply eq_add_S in Hlgth.
generalize (WFh_delete1 l2 (find l2 (witness (snd a))) Hwf2 Hwfh2);
intro Hwfhd2; generalize (WF_delete1 l2 (find l2 (witness (snd a))) Hwf2);
intro Hwfd2.
apply (IHl1 _ w Hwfh1 Hwfhd2 Hwf1 Hwfd2); [|exact Hlgth|].
intros i HH; assert (has_element l2 (find l2 i) = true).
apply Himp.
case(O.eq_real_bool (witness (snd a)) i).
rewrite <- beq_nat_refl; apply Bool.orb_true_l.
rewrite HH; apply Bool.orb_true_r.
apply (delete1_has_element_inv l2 (find l2 (witness (snd a)))) in H0.
case_eq (O.eq_real_bool (witness (snd a)) i); intro Hai;
[apply beq_real_true in Hai|apply beq_real_false in Hai].
rewrite <- Hai in HH; rewrite Hfind1 in HH.
apply (position1_has_element _ _ (S O)) in HH.
rewrite (position1_no_element _ Hwf1 _ (gt_Sn_O O)) in HH.
contradict HH; apply le_Sn_O.
destruct H0 as [Hres|Hko].
rewrite (delete1_find _ _ _ H); [exact Hres|].
rewrite (find_element1 _ _ _ (gt_Sn_O O) Hwf2
(position1_has_element _ _ _ H)).
intro Hia; apply Hai; symmetry; exact Hia.
contradict Hai.
rewrite <- (find_element1 l2 (witness (snd a)) 1 (gt_Sn_O O)
Hwf2 (position1_has_element l2 _ _ H)).
rewrite Hko in H; rewrite Hko;
rewrite (find_element1 l2 i 1 (gt_Sn_O O)
Hwf2 (position1_has_element l2 _ _ H)).
reflexivity.
rewrite (delete1_find _ _ _ H); [exact Hhd|].
rewrite (find_element1 _ _ _ (gt_Sn_O O) Hwf2
(position1_has_element _ _ _ H)).
intro Hia; apply Heqaw; symmetry; exact Hia.
Qed.

(*** INTER ***)

Fixpoint inter1 (l1 : Rlist) (l2 : Rlist) : Rlist :=
match l1 with
nil => nil
| a :: ls1 => if beq_nat (find l2 (witness (snd a))) 0
then inter1 ls1 l2
else a :: (inter1 ls1 l2)
end.

Lemma inter1_has_element :
forall l1 l2 : Rlist, forall cu : cursor,
has_element(inter1 l1 l2) cu = true -> has_element l1 cu = true.
intros l1 l2 cu; induction l1; simpl.
intro Hko; contradict Hko; apply Bool.diff_false_true.
case (beq_nat (find l2 (witness (snd a))) 0); simpl.
intro HH; rewrite (IHl1 HH); apply Bool.orb_true_r.
case (beq_nat (fst a) cu).
intros _; apply Bool.orb_true_l.
repeat(rewrite Bool.orb_false_l); apply IHl1.
Qed.

Lemma WF_inter1 :
forall l1 : Rlist, forall l2 : Rlist, well_formed l1 ->
well_formed (inter1 l1 l2).
intros l1 l2; induction l1; simpl.
auto.
case (beq_nat (find l2 (witness (snd a))) 0); simpl.
intros [_[_]]; apply IHl1.
intros [Hfst[Hhe Hwf]]; split; [exact Hfst|].
split; [|apply (IHl1 Hwf)].
case_eq (has_element (inter1 l1 l2) (fst a)).
intro Hko; apply inter1_has_element in Hko;
contradict Hko; rewrite Hhe; apply Bool.diff_false_true.
reflexivity.
Qed.

Lemma inter1_nil :
forall l : Rlist, inter1 l nil = nil.
induction l; simpl; [reflexivity | exact IHl].
Qed.

Lemma inter1_cons :
forall l1 l2 : Rlist, forall a : (cursor*element_t),
well_formed l1 ->
find l1 (witness (snd a)) = 0 -> inter1 l1 (a :: l2) = inter1 l1 l2.
induction l1; simpl.
reflexivity.
intros l2 a2;
case_eq (O.eq_real_bool (witness (snd a)) (witness (snd a2))).
intros _ [Hko _] Heq; contradict Hko; rewrite Heq; apply gt_irrefl.
case_eq (O.eq_real_bool (witness (snd a2)) (witness (snd a))); simpl.
intros Heq Hko; apply beq_real_true in Heq; contradict Hko;
rewrite Heq; rewrite beq_real_refl; apply Bool.diff_true_false.
intros _ _ [_[_ Hwf]] Hfind; rewrite(IHl1 l2 a2 Hwf Hfind);
reflexivity.
Qed.

Lemma inter1_length_ann :
forall l1 l2 : Rlist, forall a : (cursor*element_t),
fst a > 0 -> find l2 (witness(snd a)) = 0 ->
find l1 (witness (snd a)) <> 0 ->
well_formed l1 -> well_formed_hashed l1 ->
List.length (inter1 l1 (a :: l2)) = S(List.length (inter1 l1 l2)).
induction l1; simpl.
intros l2 _ _ _ Hko; contradict Hko; reflexivity.
intros l2 a2; rewrite beq_real_sym.
case_eq (O.eq_real_bool (witness (snd a2)) (witness (snd a))).
intro Heq; apply beq_real_true in Heq; rewrite <- Heq.
case_eq (beq_nat (fst a2) 0).
intros HHeq Hko; apply beq_nat_true in HHeq; contradict Hko;
rewrite HHeq; apply gt_irrefl.
intros _ Hfsta2 Hfind; rewrite Hfind; rewrite <- beq_nat_refl;
simpl.
intros _ [_[_ Hwf1]] [Hfind_l1_a2 _];
rewrite (inter1_cons _ _ _ Hwf1 Hfind_l1_a2); reflexivity.
intros _ Hfsta2 Hfindl2a2 Hfindl1a2 [_[_ Hwf1]] [_ Hh1];
case (beq_nat (find l2 (witness (snd a))) 0); simpl;
rewrite (IHl1 l2 a2 Hfsta2 Hfindl2a2 Hfindl1a2 Hwf1 Hh1);
reflexivity.
Qed.

Lemma inter1_length :
forall l1 l2 : Rlist, well_formed l1 -> well_formed l2 ->
well_formed_hashed l1 -> well_formed_hashed l2 ->
List.length (inter1 l1 l2) = List.length (inter1 l2 l1).
induction l1; simpl.
intros; rewrite inter1_nil; simpl; reflexivity.
intro l2; case_eq (beq_nat (find l2 (witness (snd a))) 0).
intros Hfindl2 [_[_ Hwf1]] Hwf2 [_ Hh1] Hh2;
apply beq_nat_true in Hfindl2.
rewrite (inter1_cons l2 l1 a Hwf2 Hfindl2).
apply (IHl1 l2 Hwf1 Hwf2 Hh1 Hh2).
intros Hfindl2 [Hfsta[_ Hwf1]] Hwf2 [Hfindl1 Hh1] Hh2; simpl;
apply beq_nat_false in Hfindl2.
rewrite (inter1_length_ann l2 l1 a Hfsta Hfindl1 Hfindl2 Hwf2 Hh2).
rewrite (IHl1 l2 Hwf1 Hwf2 Hh1 Hh2); reflexivity.
Qed.

Lemma inter1_contains :
forall l1 l2 : Rlist, forall w : R,
well_formed l1 -> well_formed l2 ->
has_element l1 (find l1 w) = true ->
has_element l2 (find l2 w) = true ->
has_element (inter1 l1 l2) (find (inter1 l1 l2) w) = true.
intros l1 l2 w; induction l1; simpl.
intros _ _ Hko; contradict Hko; apply Bool.diff_false_true.
case_eq(O.eq_real_bool (witness (snd a)) w).
intros Heq _ Hwf2 _; apply beq_real_true in Heq; rewrite <- Heq.
case_eq (beq_nat (find l2 (witness (snd a))) 0); simpl.
intros Hnil Hko; apply beq_nat_true in Hnil;
apply (position1_has_element _ _ 1) in Hko; contradict Hko; rewrite Hnil;
rewrite (position1_no_element _ Hwf2 _ (gt_Sn_O O)); apply le_Sn_n.
rewrite beq_real_refl; rewrite <- beq_nat_refl; simpl; reflexivity.
case (beq_nat(find l2 (witness (snd a))) O); simpl.
case_eq (beq_nat (fst a) (find l1 w)).
intro Heq; destruct (find_has_element l1 w) as [Heq2 | Heq2];
apply beq_nat_true in Heq;
[intros _ [_[Hko]]|intros _ [Hko]]; contradict Hko; rewrite Heq;
rewrite Heq2; [apply Bool.diff_true_false|apply gt_irrefl].
rewrite Bool.orb_false_l; intros _ _ [_[_ Hwf1]] Hwf2 Hf1 Hf2.
apply (IHl1 Hwf1 Hwf2 Hf1 Hf2).
intro He; rewrite He; simpl.
case_eq (beq_nat (fst a) (find l1 w)).
intro Heq; destruct (find_has_element l1 w) as [Heq2 | Heq2];
apply beq_nat_true in Heq;
[intros [_[Hko]]|intros [Hko]]; contradict Hko; rewrite Heq;
rewrite Heq2; [apply Bool.diff_true_false|apply gt_irrefl].
rewrite Bool.orb_false_l; intros _ [_[_ Hwf1]] Hwf2 Hf1 Hf2.
rewrite (IHl1 Hwf1 Hwf2 Hf1 Hf2); apply Bool.orb_true_r.
Qed.

Lemma inter1_contains_inv :
forall l1 l2 : Rlist, forall w : R,
well_formed l1 -> well_formed l2 ->
has_element (inter1 l1 l2) (find (inter1 l1 l2) w) = true ->
has_element l1 (find l1 w) = true /\
has_element l2 (find l2 w) = true.
intros l1 l2 w; induction l1; simpl.
intros _ _ Hko; contradict Hko; apply Bool.diff_false_true.
case_eq (O.eq_real_bool (witness (snd a)) w).
intro Heq; apply beq_real_true in Heq; rewrite <- Heq.
destruct (find_has_element l2 (witness (snd a))) as [Hhe | Hko].
intros _ _ _; rewrite <- beq_nat_refl; split;
[apply Bool.orb_true_l|exact Hhe].
rewrite Hko; rewrite <- beq_nat_refl; simpl.
intros [_[_ Hwf1]] Hwf2 Hhinter; rewrite <- Heq in IHl1;
destruct (IHl1 Hwf1 Hwf2 Hhinter) as [_ Hh2];
apply (position1_has_element _ _ 1) in Hh2; contradict Hh2.
rewrite Hko; rewrite (position1_no_element l2 Hwf2 1 (gt_Sn_O O));
apply le_Sn_n.
case_eq (beq_nat (find l2 (witness (snd a))) 0); simpl.
intros _ _ [_[_ Hwf1]] Hwf2 Hhinter;
destruct (IHl1 Hwf1 Hwf2 Hhinter) as [Hhe1 Hhe2].
rewrite Hhe1; split; [apply Bool.orb_true_r|exact Hhe2].
intros _ Hee; rewrite Hee; simpl.
case_eq (beq_nat (fst a) (find (inter1 l1 l2) w)).
intro Heq; destruct (find_has_element (inter1 l1 l2) w) as [Heq2 | Heq2];
apply beq_nat_true in Heq; [intros [_[Hko]];
apply inter1_has_element in Heq2|intros [Hko]];
contradict Hko; rewrite Heq;
rewrite Heq2; [apply Bool.diff_true_false|apply gt_irrefl].
rewrite Bool.orb_false_l; intros _ [_[_ Hwf1]] Hwf2 Hhinter;
destruct (IHl1 Hwf1 Hwf2 Hhinter) as [Hhe1 Hhe2].
rewrite Hhe1; split; [apply Bool.orb_true_r|exact Hhe2].
Qed.

Lemma inter1_insert1 :
forall l1 l2 : Rlist, forall b cu : cursor, forall e : element_t,
well_formed l1 -> find l1 (witness e) = 0 ->
inter1 l1 (insert1 l2 b cu e) = inter1 l1 l2.
induction l1; simpl.
reflexivity.
intros l2 b cu e;
case_eq (O.eq_real_bool (witness (snd a)) (witness e)); simpl.
intros _ [Hko _] Heq; contradict Hko; rewrite Heq; apply gt_irrefl.
intro Hdiff; apply beq_real_false in Hdiff;
rewrite <- (insert1_find _ _ _ _ _ Hdiff).
case (beq_nat (find l2 (witness (snd a))) 0); simpl.
intros [_[_]]; apply IHl1.
intros [_[_ Hwf]] Hfind; rewrite (IHl1 l2 b cu e Hwf Hfind);
reflexivity.
Qed.

Lemma inter1_delete1 :
forall l1 l2 : Rlist, forall w : R,
well_formed l1 -> well_formed l2 -> find l1 w = 0 ->
has_element l2 (find l2 w) = true ->
inter1 l1 (delete1 l2 (find l2 w)) = inter1 l1 l2.
induction l1; simpl.
reflexivity.
intros l2 w;
case_eq (O.eq_real_bool (witness (snd a)) w); simpl.
intros _ [Hko _] _ Heq; contradict Hko; rewrite Heq; apply gt_irrefl.
intros Hdiff [_[_ Hwf1]] Hwf2 Hfindl1 Hhel2;
apply beq_real_false in Hdiff; rewrite (delete1_find _ _ _ Hhel2);
[|rewrite (find_element1 _ _ _ (gt_Sn_O O) Hwf2
(position1_has_element _ _ _ Hhel2)); exact Hdiff].
case (beq_nat (find l2 (witness (snd a))) 0); simpl.
apply (IHl1 _ _ Hwf1 Hwf2 Hfindl1 Hhel2).
rewrite (IHl1 l2 w Hwf1 Hwf2 Hfindl1 Hhel2);
reflexivity.
Qed.

Definition inter (l1 : list) (l2 : list) :=
Build_list (inter1 l1 l2) (WF_inter1 l1 l2 (wf l1)).

Lemma inter_length :
forall l1 l2 : list,
well_formed_hashed l1 -> well_formed_hashed l2 ->
length (inter l1 l2) = length (inter l2 l1).
intros [l1 Hwf1] [l2 Hwf2]; unfold length; unfold inter; simpl.
apply (inter1_length l1 l2 Hwf1 Hwf2).
Qed.

Lemma inter_contains :
forall l1 l2 : list, forall w : R,
has_element l1 (find l1 w) = true ->
has_element l2 (find l2 w) = true ->
has_element (inter l1 l2) (find (inter l1 l2) w) = true.
intros [l1 Hwf1] [l2 Hwf2] w; unfold inter; simpl.
apply (inter1_contains l1 l2 w Hwf1 Hwf2).
Qed.

Lemma inter_contains_inv :
forall l1 l2 : list, forall w : R,
has_element (inter l1 l2) (find (inter l1 l2) w) = true ->
has_element l1 (find l1 w) = true /\
has_element l2 (find l2 w) = true.
intros [l1 Hwf1] [l2 Hwf2] w; unfold inter; simpl.
apply (inter1_contains_inv l1 l2 w Hwf1 Hwf2).
Qed.

(*** UNION ***)

Fixpoint union1 (l1 : Rlist) (l2 : Rlist)
(pos : Rlist -> element_t -> nat) : Rlist :=
match l1 with
nil => l2
| a :: ls1 => if beq_nat (find l2 (witness (snd a))) 0 then
union1 ls1 (insert1 l2 (pos l2 (snd a)) (New_Max.new l2) (snd a)) pos
else union1 ls1 l2 pos
end.

Lemma WF_union1 :
forall pos : Rlist -> element_t -> nat,
forall l1 : Rlist, forall l2 : Rlist,
well_formed l2 ->
well_formed (union1 l1 l2 pos).
intro pos; induction l1; simpl.
intros l2 Hex; exact Hex.
intros l2; case (beq_nat (find l2 (witness (snd a))) 0).
intros Hwf2; apply (WF_insert l2 (pos l2 (snd a)) (snd a)) in Hwf2.
apply (IHl1 _ Hwf2).
apply IHl1.
Qed.

Lemma union1_length :
forall pos : Rlist -> element_t -> nat,
forall l1 l2 : Rlist,
well_formed l1 -> well_formed_hashed l1 ->
List.length (union1 l1 l2 pos) + List.length (inter1 l1 l2)
= List.length l1 + List.length l2.
intro pos; induction l1; simpl.
intros l2; rewrite plus_comm; simpl; reflexivity.
intros l2; case_eq (beq_nat (find l2 (witness (snd a))) 0); simpl.
intros _ [_[_ Hwf1]] [Hfindl1 Hh1];
rewrite plus_n_Sm;
rewrite <- (insert1_length l2 (pos l2 (snd a)) (New_Max.new l2)
(snd a)); rewrite <- (IHl1 _ Hwf1 Hh1).
rewrite (inter1_insert1 l1 l2 _ _ _ Hwf1 Hfindl1); reflexivity.
intros _ [_[_ Hwf1]] [_ Hh1]; rewrite <- (IHl1 _ Hwf1 Hh1).
rewrite plus_n_Sm; simpl; reflexivity.
Qed.

Lemma union1_contains :
forall pos : Rlist -> element_t -> nat,
forall l1 l2 : Rlist, forall w : R,
well_formed l1 -> well_formed l2 ->
has_element l1 (find l1 w) = true \/
has_element l2 (find l2 w) = true ->
has_element (union1 l1 l2 pos) (find (union1 l1 l2 pos) w) = true.
intros pos; induction l1; simpl.
intros l2 w _ _ [Hko | Hex];
[contradict Hko; apply Bool.diff_false_true|exact Hex].
intros l2 w; case_eq (beq_nat (find l2 (witness (snd a))) 0); simpl.
case_eq (O.eq_real_bool (witness (snd a)) w); simpl.
intro Heq; apply beq_real_true in Heq; rewrite <- Heq;
intros _ [_[_ Hwf1]] Hwf2 _.
apply (IHl1 _ _ Hwf1 (WF_insert _ _ _ Hwf2)).
rewrite <- (insert1_element1_new l2 Hwf2 (pos l2 (snd a)) _
_ (New_Max.new_has_element l2)) at 6.
right; apply (has_element_position1 _ _ 1);
apply (find_element1_rev (insert1 l2 (pos l2 (snd a))
(New_Max.new l2) (snd a)));
[apply gt_Sn_O|apply position1_has_element; apply has_element_insert1_new].
case_eq (beq_nat (fst a) (find l1 w)).
intros Heq _ _; destruct (find_has_element l1 w) as [Heq2 | Heq2];
apply beq_nat_true in Heq; [intros [_[Hko]]|intros [Hko]];
contradict Hko; rewrite Heq;
rewrite Heq2; [apply Bool.diff_true_false|apply gt_irrefl].
rewrite Bool.orb_false_l.
intros _ Hdiff _ [_[_ Hwf1]] Hwf2 Hor;
apply (IHl1 _ _ Hwf1 (WF_insert _ _ _ Hwf2)).
destruct Hor as [Hhe1|Hhe2]; [left; exact Hhe1|right].
apply beq_real_false in Hdiff; rewrite <- insert1_find.
apply insert1_has_element; exact Hhe2.
intro He; contradict Hdiff; symmetry; exact He.
case_eq (O.eq_real_bool (witness (snd a)) w).
intro Heqwa; apply beq_real_true in Heqwa; rewrite Heqwa.
intros Hdiff [_[_ Hwf1]] Hwf2 _; apply (IHl1 _ _ Hwf1 Hwf2).
right; destruct (find_has_element l2 w) as [Hex|Hko];
[exact Hex|contradict Hdiff; rewrite Hko; rewrite <- beq_nat_refl;
apply Bool.diff_true_false].
case_eq (beq_nat (fst a) (find l1 w)).
intros Heq _ _; destruct (find_has_element l1 w) as [Heq2 | Heq2];
apply beq_nat_true in Heq; [intros [_[Hko]]|intros [Hko]];
contradict Hko; rewrite Heq;
rewrite Heq2; [apply Bool.diff_true_false|apply gt_irrefl].
rewrite Bool.orb_false_l.
intros _ _ _ [_[_]]; apply IHl1.
Qed.

Lemma union1_contains_inv :
forall pos : Rlist -> element_t -> nat,
forall l1 l2 : Rlist, forall w : R,
well_formed l1 -> well_formed l2 ->
has_element (union1 l1 l2 pos) (find (union1 l1 l2 pos) w) = true ->
has_element l1 (find l1 w) = true \/
has_element l2 (find l2 w) = true.
intro pos; induction l1; simpl.
intros l2 w _ _ Hex; right; exact Hex.
intros l2 w;
case_eq (beq_nat (find l2 (witness (snd a))) 0); simpl.
case_eq (O.eq_real_bool (witness (snd a)) w); simpl.
rewrite <- beq_nat_refl; left; apply Bool.orb_true_l.
intros Hdiff Hfind [_[_ Hwf1]] Hwf2 Hunion.
rewrite beq_real_sym in Hdiff; apply beq_real_false in Hdiff;
apply beq_nat_true in Hfind.
apply (IHl1 _ _ Hwf1 (WF_insert _ _ _ Hwf2)) in Hunion.
destruct Hunion as [Hhe1 | Hi];
[left; rewrite Hhe1; apply Bool.orb_true_r|right].
rewrite <- (insert1_find _ _ _ _ _ Hdiff) in Hi.
apply has_element_insert1 in Hi; destruct Hi as [Heq|Hex];
[|exact Hex].
destruct (find_has_element l2 w) as [Heq2 |Heq2];
[contradict Heq2; rewrite <- Heq; rewrite New_Max.new_has_element;
apply Bool.diff_false_true|
symmetry in Heq; generalize (New_Max.new_valid l2); intro Hko;
contradict Hko; rewrite <- Heq; rewrite Heq2; apply gt_irrefl].
case_eq (O.eq_real_bool (witness (snd a)) w).
rewrite <- beq_nat_refl; left; apply Bool.orb_true_l.
intros _ _ [_[_ Hwf1]] Hwf2 Hunion;
destruct (IHl1 _ _ Hwf1 Hwf2 Hunion) as [He1|He2];
[rewrite He1; left; apply Bool.orb_true_r|right; exact He2].
Qed.

(*** DIFF ***)

Fixpoint diff1 (l1 : Rlist) (l2 : Rlist) : Rlist :=
match l2 with
nil => l1
| a :: ls2 => if beq_nat (find l1 (witness (snd a))) 0 then
diff1 l1 ls2 else diff1 (delete1 l1 (find l1 (witness (snd a)))) ls2
end.

Lemma WF_diff1 :
forall l2 : Rlist, forall l1 : Rlist,
well_formed l1 ->
well_formed (diff1 l1 l2).
induction l2; simpl.
intros l1 Hex; exact Hex.
intros l1; case (beq_nat (find l1 (witness (snd a))) 0).
apply IHl2.
intros Hwf1; apply (WF_delete1 l1 (find l1 (witness (snd a)))) in Hwf1.
apply (IHl2 _ Hwf1).
Qed.

Lemma diff1_length :
forall l1 l2 : Rlist,
well_formed l1 -> well_formed l2 ->
well_formed_hashed l1 -> well_formed_hashed l2 ->
List.length (diff1 l2 l1) + List.length (inter1 l2 l1)
= List.length l2.
intros l1 l2 Hwf1 Hwf2 Hh1 Hh2;
rewrite (inter1_length _ _ Hwf2 Hwf1 Hh2 Hh1);
generalize l2 Hwf1 Hwf2 Hh1; clear; induction l1; simpl.
intros l2; rewrite plus_comm; simpl; reflexivity.
intros l2; case_eq (beq_nat (find l2 (witness (snd a))) 0); simpl.
intros _ [_[_ Hwf1]] Hwf2 [_ Hh1]; apply (IHl1 _ Hwf1 Hwf2 Hh1).
intros Hfindl2 [_[_ Hwf1]] Hwf2 [Hfindl1 Hh1];
apply beq_nat_false in Hfindl2.
destruct (find_has_element l2 (witness (snd a))) as [Hhe|Hko];
[|contradict Hfindl2; apply Hko].
rewrite (delete1_length l2 (find l2 (witness (snd a))) 1
(position1_has_element _ _ 1 Hhe)).
rewrite <- plus_n_Sm.
rewrite <- (inter1_delete1 _ _ _ Hwf1 Hwf2 Hfindl1 Hhe).
rewrite (IHl1 _ Hwf1 (WF_delete1 _ _ Hwf2) Hh1); reflexivity.
Qed.

Lemma diff1_contains :
forall l2 l1 : Rlist, forall w : R,
well_formed l1 -> well_formed l2 ->
has_element l1 (find l1 w) = true ->
has_element l2 (find l2 w) = false ->
has_element (diff1 l1 l2) (find (diff1 l1 l2) w) = true.
induction l2; simpl.
intros l1 w _ _ Hex _; exact Hex.
intros l1 w; case_eq (O.eq_real_bool (witness (snd a)) w); simpl.
rewrite <- beq_nat_refl; rewrite Bool.orb_true_l;
intros _ _ _ _ Hko; contradict Hko; apply Bool.diff_true_false.
case (beq_nat (fst a) (find l2 w)); simpl.
intros _ _ _ _ Hko; contradict Hko; apply Bool.diff_true_false.
case_eq (beq_nat (find l1 (witness (snd a))) 0); simpl.
intros _ _ Hwf1 [_[_]]; apply (IHl2 l1 w Hwf1).
intros Hdfind Hdiff Hwf1 [_[_ Hwf2]] Hhe1 Hhe2;
apply beq_nat_false in Hdfind; apply beq_real_false in Hdiff;
destruct (find_has_element l1 (witness (snd a))) as [Hhe|Hko];
[|contradict Hdfind; apply Hko].
apply (IHl2 _ w (WF_delete1 _ _ Hwf1) Hwf2); [|exact Hhe2].
rewrite (delete1_find _ _ _ Hhe);
[|rewrite (find_element1 _ _ _ (gt_Sn_O O) Hwf1 (position1_has_element
_ _ _ Hhe)); intro HH; apply Hdiff; symmetry; exact HH].
destruct (delete1_has_element_inv _ (find l1 (witness (snd a))) _ Hhe1);
[exact H|].
contradict Hdiff; rewrite <- (find_element1 _ _ _ (gt_Sn_O O) Hwf1
(position1_has_element _ _ _ Hhe)); rewrite H;
rewrite (find_element1 _ _ _ (gt_Sn_O O) Hwf1
(position1_has_element _ _ _ Hhe1)); reflexivity.
Qed.

Lemma diff1_contains_inv :
forall l2 l1 : Rlist, forall w : R,
well_formed l1 -> well_formed l2 ->
well_formed_hashed l1 ->
has_element (diff1 l1 l2) (find (diff1 l1 l2) w) = true ->
has_element l1 (find l1 w) = true /\
has_element l2 (find l2 w) = false.
induction l2; simpl.
intros l1 w _ _ _ Hex; split; [exact Hex|reflexivity].
intros l1 w;
case_eq (beq_nat (find l1 (witness (snd a))) 0); simpl.
intros Hfind1 Hwf1 [Hfsta[_ Hwf2]] Hh1 Hdiff;
destruct (IHl2 l1 _ Hwf1 Hwf2 Hh1 Hdiff) as [Hhe1 Hhe2].
split; [exact Hhe1|].
case_eq (O.eq_real_bool (witness (snd a)) w); simpl.
intro Heq; apply beq_real_true in Heq; apply beq_nat_true in Hfind1;
apply (position1_has_element l1 _ 1) in Hhe1; contradict Hhe1;
rewrite <- Heq; rewrite Hfind1; rewrite (position1_no_element l1 Hwf1 1
(gt_Sn_O O)); apply gt_irrefl.
case_eq (beq_nat (fst a) (find l2 w)).
intro Heq; apply beq_nat_true in Heq;
destruct (find_has_element l2 w) as [Heq2 | Heq2];
[contradict Hhe2|contradict Hfsta; rewrite Heq];
rewrite Heq2; [apply Bool.diff_true_false|apply gt_irrefl].
intros; rewrite Bool.orb_false_l; exact Hhe2.
intros Hfind1 Hwf1 [Hfsta[_ Hwf2]] Hh1 Hdiff;
apply beq_nat_false in Hfind1;
destruct (find_has_element l1 (witness (snd a))) as [Hhe1find|Hko];
[|contradict Hfind1; exact Hko].
destruct (IHl2 _ _ (WF_delete1 _ _ Hwf1) Hwf2 (WFh_delete1 _ _ Hwf1 Hh1)
Hdiff) as [Hhe1 Hhe2].
case_eq (O.eq_real_bool (witness (snd a)) w); simpl.
intro Heq; apply beq_real_true in Heq; rewrite <- Heq in Hhe1.
generalize (find_element1 l1 _ 1 (gt_Sn_O O) Hwf1
(position1_has_element _ _ _ Hhe1find)); intro Heqa;
rewrite <- Heqa in Hhe1 at 3.
rewrite (delete1_find_deleted _ _ Hhe1find Hwf1 Hh1) in Hhe1.
apply (position1_has_element _ _ 1) in Hhe1; contradict Hhe1;
rewrite (position1_no_element _ (WF_delete1 _ _ Hwf1) 1 (gt_Sn_O O));
apply gt_irrefl.
rewrite beq_real_sym; intro Hneq; apply beq_real_false in Hneq;
rewrite (delete1_find _ _ _ Hhe1find) in Hhe1;
[|rewrite (find_element1 _ _ 1 (gt_Sn_O O) Hwf1
(position1_has_element _ _ _ Hhe1find)); exact Hneq].
apply (delete1_has_element _ _ _ Hwf1) in Hhe1;
destruct Hhe1 as [Hhe1 _].
rewrite Hhe2; rewrite Bool.orb_false_r; split; [exact Hhe1|].
case_eq(beq_nat (fst a) (find l2 w)); [|reflexivity].
intro Heq; apply beq_nat_true in Heq;
destruct (find_has_element l2 w) as [Heq2 | Heq2];
[contradict Hhe2|contradict Hfsta; rewrite Heq];
rewrite Heq2; [apply Bool.diff_true_false|apply gt_irrefl].
Qed.

Definition diff (l1 : list) (l2 : list) :=
Build_list (diff1 l1 l2) (WF_diff1 l2 l1 (wf l1)).

Lemma diff_length :
forall l1 l2 : list,
well_formed_hashed l1 -> well_formed_hashed l2 ->
length (diff l1 l2) + length (inter l1 l2) = length l1.
intros [l1 Hwf1] [l2 Hwf2]; simpl; intros Hh1 Hh2;
unfold length; unfold inter; unfold diff; simpl.
apply (diff1_length l2 l1 Hwf2 Hwf1 Hh2 Hh1).
Qed.

Lemma diff_contains :
forall l1 l2 : list, forall w : R,
has_element l1 (find l1 w) = true ->
has_element l2 (find l2 w) = false ->
has_element (diff l1 l2) (find (diff l1 l2) w) = true.
intros [l1 Hwf1] [l2 Hwf2] w; unfold diff; simpl.
apply (diff1_contains l2 l1 w Hwf1 Hwf2).
Qed.

Lemma diff_contains_inv :
forall l1 l2 : list, forall w : R,
well_formed_hashed l1 -> 
has_element (diff l1 l2) (find (diff l1 l2) w) = true ->
has_element l1 (find l1 w) = true /\
has_element l2 (find l2 w) = false.
intros [l1 Hwf1] [l2 Hwf2] w; unfold diff; simpl.
apply (diff1_contains_inv l2 l1 w Hwf1 Hwf2).
Qed.

(*** REPLACE_ELT ***)

Definition replace_elt1 (pos : Rlist -> element_t -> nat) (l :Rlist)
(cu : nat) (e : element_t) : Rlist :=
if has_element l cu then insert1 (delete1 l cu) (pos l e) cu e
else l.

Lemma WF_replace_elt1 :
forall pos : Rlist -> element_t -> nat,
forall l : Rlist, forall cu : cursor, forall e : element_t,
well_formed l -> well_formed (replace_elt1 pos l cu e).
intros pos l cu e Hwf; unfold replace_elt1; case_eq (has_element l cu).
intro Hhe; apply WF_insert1.
generalize Hwf Hhe; clear; induction l; simpl.
intros _ Hko; contradict Hko; apply Bool.diff_false_true.
case_eq (beq_nat (fst a) cu).
intros Heq [Hfst _] _; apply beq_nat_true in Heq;
rewrite <- Heq; apply Hfst.
rewrite Bool.orb_false_l; intros _ [_[_]]; apply IHl.
case_eq (has_element (delete1 l cu) cu); [|reflexivity].
intro HH; destruct (delete1_has_element l _ _ Hwf HH) as [_ Hko];
contradict Hko; reflexivity.
apply WF_delete1; exact Hwf.
intros _; exact Hwf.
Qed.

Lemma replace_elt1_length :
forall pos : Rlist -> element_t -> nat,
forall l : Rlist, forall cu : cursor, forall e : element_t,
List.length l = List.length (replace_elt1 pos l cu e).
intros pos l cu e; unfold replace_elt1.
case_eq (has_element l cu); [|reflexivity].
intro Hhe; rewrite insert1_length;
apply (delete1_length l cu 1); apply position1_has_element;
exact Hhe.
Qed.

Lemma replace_elt1_has_element :
forall pos : Rlist -> element_t -> nat,
forall l : Rlist, forall cu cun : cursor, forall e : element_t,
well_formed l ->
has_element l cun = has_element (replace_elt1 pos l cu e) cun.
intros pos l cu cun e Hwf; unfold replace_elt1;
case_eq (has_element l cu); [|reflexivity].
intro Hhecu; case_eq (has_element l cun); intro Hhecun.
symmetry; case_eq (beq_nat cu cun).
intro Heq; apply beq_nat_true in Heq; rewrite Heq;
apply has_element_insert1_new.
intro Hdiff; apply insert1_has_element;
destruct (delete1_has_element_inv l cu cun Hhecun) as [Hex|Heq].
exact Hex.
contradict Heq; apply (beq_nat_false); exact Hdiff.
case_eq (has_element (insert1 (delete1 l cu) (pos l e) cu e) cun);
[|reflexivity].
intro Hheicun; apply has_element_insert1 in Hheicun.
destruct Hheicun as [Heq|Hhedcun];
[contradict Hhecu; rewrite Heq; rewrite Hhecun;
apply Bool.diff_false_true|].
apply delete1_has_element in Hhedcun.
destruct Hhedcun as [Hhecuninv _]; contradict Hhecuninv;
rewrite Hhecun; apply Bool.diff_false_true.
exact Hwf.
Qed.

Lemma replace_elt1_element1 :
forall pos : Rlist -> element_t -> nat,
forall l : Rlist, forall cu cun : cursor, forall e : element_t,
well_formed l -> cu <> cun -> has_element l cun = true ->
element1 l cun = element1 (replace_elt1 pos l cu e) cun.
intros pos l cu cun e Hwf Hdiff Hhecun; unfold replace_elt1.
case_eq (has_element l cu); intro Hhecu; [|reflexivity].
rewrite <- (insert1_element1_old _ (WF_delete1 l cu Hwf)
 _ _ _ _ 1 (gt_Sn_O O)).
symmetry; apply (delete1_element1 _ _ _ 1).
apply (position1_has_element _ _ _ Hhecu).
intro Heq; symmetry in Heq; apply (Hdiff Heq).
case_eq (has_element (delete1 l cu) cu); [|reflexivity]; intro Hko;
apply (position1_has_element _ _ 1) in Hko; contradict Hko;
rewrite (delete1_position1_deleted l Hwf cu 1
(position1_has_element _ _ _ Hhecu)); apply le_Sn_n.
destruct (delete1_has_element_inv l cu cun Hhecun) as [Hhedcun | Hko].
apply (position1_has_element _ _ _ Hhedcun).
elim (Hdiff Hko).
Qed.

Lemma replace_elt1_element1_replaced :
forall pos : Rlist -> element_t -> nat,
forall l : Rlist, forall cu : cursor, forall e : element_t,
well_formed l -> has_element l cu = true ->
element1 (replace_elt1 pos l cu e) cu = e.
intros pos l cu e Hwf Hhecu; unfold replace_elt1.
rewrite Hhecu; apply (insert1_element1_new _ (WF_delete1 l cu Hwf)).
case_eq (has_element (delete1 l cu) cu); [|reflexivity]; intro Hko;
apply (position1_has_element _ _ 1) in Hko; contradict Hko;
rewrite (delete1_position1_deleted l Hwf cu 1
(position1_has_element _ _ _ Hhecu)); apply le_Sn_n.
Qed.

Lemma replace_elt1_find :
forall pos : Rlist -> element_t -> nat,
forall l : Rlist, forall cu : cursor, forall e : element_t,
forall w : R, well_formed l -> well_formed_hashed l ->
 witness e <> w -> find l w <> cu ->
find l w = find (replace_elt1 pos l cu e) w.
intros pos l cu e w Hwf Hh Hdiff Hfind; unfold replace_elt1.
case_eq (has_element l cu); [|reflexivity].
intro Hhecu; rewrite <- insert1_find.
symmetry; apply (delete1_find _ _ _ Hhecu).
intro Heq; apply Hfind; rewrite Heq;
apply (position1_has_element _ _ 1) in Hhecu;
apply position_eq with (Build_list l Hwf); unfold position; simpl;
rewrite (find_position1_inv l Hh Hwf cu 1 Hhecu);
[exact Hhecu|reflexivity].
intro Heq; symmetry in Heq; elim (Hdiff Heq).
Qed.

Lemma replace_elt1_find_replaced :
forall pos : Rlist -> element_t -> nat,
forall l : Rlist, forall cu : cursor, forall e : element_t,
well_formed l -> well_formed_hashed l -> has_element l cu = true ->
find l (witness e) = 0 \/ find l (witness e) = cu ->
find (replace_elt1 pos l cu e) (witness e) = cu.
intros pos l cu e Hwf Hh Hhecu [Hfind|Hfind]; unfold replace_elt1;
rewrite Hhecu; apply (insert1_find_new _ _ _ _ (WF_delete1 l cu Hwf)).
case_eq (O.eq_real_bool (witness e) (witness (element1 l cu))).
intro Heq; apply beq_real_true in Heq;
apply (position1_has_element _ _ 1) in Hhecu;
generalize Hhecu; intro Hko; contradict Hko.
rewrite <- (find_position1_inv l Hh Hwf cu 1 Hhecu).
rewrite <- Heq; rewrite Hfind;
rewrite (position1_no_element l Hwf _ (gt_Sn_O O));
apply gt_irrefl.
intro Hdiff; apply beq_real_false in Hdiff;
rewrite <- Hfind; apply (delete1_find l _ cu Hhecu Hdiff).
rewrite <- (find_element1 l _ 1 (gt_Sn_O O) Hwf).
rewrite Hfind; apply (delete1_find_deleted l cu Hhecu Hwf Hh).
rewrite Hfind; apply position1_has_element; exact Hhecu.
Qed.

(*** SPECIFIC TO HASHED ***)

(*** EMPTY ***)

Lemma WF_hnil : well_formed_hashed nil.
simpl.
auto.
Qed.

Definition hempty : hset :=
Build_hset empty WF_hnil.

(*** LEFT ***)

Lemma left1_hashed :
forall l : Rlist, forall cu : cursor,
well_formed_hashed l -> well_formed_hashed (left1 l cu).
intros l cu; induction l; simpl.
auto.
case (beq_nat (fst a) cu); simpl.
auto.
intros [Hfind Hwf]; split; [|apply(IHl Hwf)].
generalize Hfind; clear; induction l; simpl.
auto.
case(beq_nat (fst a0) cu); simpl.
auto.
case (O.eq_real_bool (witness (snd a0)) (witness (snd a))).
intro H; exact H.
intro H; apply (IHl H).
Qed.

Lemma WF_hleft :
forall l : list, forall cu : cursor,
well_formed_hashed l -> well_formed_hashed (left l cu).
intros [l H] cu; unfold left; case (beq_nat cu 0); simpl.
auto.
apply left1_hashed.
Qed.

Definition hleft (m : hset) (cu : cursor) : hset :=
if beq_nat cu 0 then m
else Build_hset (left m cu) (WF_hleft m cu (hwf m)).

(*** RIGHT ***)

Lemma right1_hashed :
forall l : Rlist, forall cu : cursor,
well_formed_hashed l -> well_formed_hashed (right1 l cu).
intros l cu; induction l; simpl.
auto.
case (beq_nat (fst a) cu); simpl.
auto.
intros [_ Hwf]; apply (IHl Hwf).
Qed.

Lemma WF_hright :
forall l : list, forall cu : cursor,
well_formed_hashed l -> well_formed_hashed (right l cu).
intros [l H] cu; unfold right; case (beq_nat cu 0); simpl.
auto.
apply right1_hashed.
Qed.

Definition hright (m : hset) (cu : cursor) : hset :=
if beq_nat cu 0 then hempty
else Build_hset (right m cu) (WF_hright m cu (hwf m)).

(*** INSERT ***)

Lemma WFh_insert1 :
forall l : Rlist, forall e : element_t,
forall cun : cursor,
well_formed l -> well_formed_hashed l ->
well_formed_hashed (if beq_nat (find l (witness e)) 0 then 
insert1 l (first1 l) (New_Max.new l) e else l).
intros l e cun Hwf.
destruct (find_has_element l (witness e)) as [Hhe|Hfind].
case_eq (beq_nat(find l (witness e)) 0).
intro Heq; apply beq_nat_true in Heq;
apply (position1_has_element l _ 1) in Hhe; contradict Hhe; rewrite Heq;
rewrite (position1_no_element l Hwf 1 (gt_Sn_O O)); apply gt_not_le;
apply gt_Sn_n.
auto.
rewrite Hfind; rewrite <- beq_nat_refl;
generalize Hfind; clear; case l; simpl.
auto.
intros a ll; rewrite <- beq_nat_refl; simpl.
case (O.eq_real_bool (witness (snd a)) (witness e)).
intros Heq Hh; split; [exact Heq|exact Hh].
intros Heq Hh; split; [exact Heq|exact Hh].
Qed.

Module Type Insert.
Parameter insert : hset -> element_t -> hset.

Axiom insert_has_element :
forall l : hset, forall e : element_t, forall cun : cursor,
find l (witness e) = 0 -> position (insert l e) cun > 0 ->
cun = New_Max.new l \/ position l cun > 0.
Axiom insert_has_element_new :
forall l : hset, forall e : element_t, find l (witness e) = 0 ->
position (insert l e) (New_Max.new l) > 0.
Axiom  insert_has_element_rev :
forall l : hset, forall e : element_t, forall cun : cursor,
find l (witness e) = 0 -> position l cun > 0 ->
position (insert l e) cun > 0.

Axiom insert_length :
forall (l : hset), forall (e : element_t),
find l (witness e) = 0 -> length (insert l e) = length l + 1.

Axiom insert_element_old :
forall l : hset, forall e : element_t, forall cun : cursor,
find l (witness e) = 0 ->
position l cun > 0 -> element l cun = element (insert l e) cun.
Axiom insert_element_new :
forall l : hset, forall e : element_t,
find l (witness e) = 0 -> element (insert l e) (New_Max.new l) = e.

Axiom insert_find :
forall l : hset, forall w : R, forall e : element_t,
find l (witness e) = 0 -> w <> witness e ->
find l w = find (insert l e) w.
Axiom insert_find_new :
forall l : hset, forall e : element_t,
find l (witness e) = 0 ->
find (insert l e) (witness e) = New_Max.new l.

End Insert.

Module Ins : Insert.

Definition insertl (l : Rlist) (e : element_t) : Rlist :=
if beq_nat (find l (witness e)) 0 then 
insert1 l (first1 l) (New_Max.new l) e else l.

Lemma WF_insert : forall l : Rlist, forall e : element_t,
well_formed l ->
well_formed (insertl l e).
intros l e H; unfold insertl; simpl.
case (beq_nat (find l (witness e)) 0); [| exact H].
apply (WF_insert1 l _ e _ (New_Max.new_valid l)
(New_Max.new_has_element l) H).
Qed.

Lemma WFh_insert : forall l : list, forall e : element_t,
well_formed_hashed l ->
well_formed_hashed (insertl l e).
intros [l H] e; unfold insertl; unfold Raw_List.insert;
unfold first; simpl.
intros Ho; apply (WFh_insert1 l e (New_Max.new l) H) in Ho.
generalize Ho;
case (beq_nat (find l (witness e)) 0); simpl;
intro Hr; exact Hr.
Qed.

Definition insert (l : hset) (e : element_t) : hset :=
Build_hset (Build_list (insertl l e) (WF_insert l e (wf l)))
(WFh_insert l e (hwf l)).

Lemma hinsert_is_insert :
forall l : hset, forall e : element_t,
find l (witness e) = 0 ->
this(hthis(insert l e)) = this(Raw_List.insert l (first l) e).
intros [[l Hwf] Hh] e; unfold Raw_List.insert;
unfold first; simpl; unfold insertl.
intro Hfind; rewrite Hfind; rewrite <- beq_nat_refl.
reflexivity.
Qed.

Lemma insert_has_element :
forall l : hset, forall e : element_t, forall cun : cursor,
find l (witness e) = 0 -> position (insert l e) cun > 0 ->
cun = New_Max.new l \/ position l cun > 0.
intros l e cun Hfind; unfold position;
rewrite (hinsert_is_insert l e Hfind);
apply insert_has_element.
Qed.

Lemma insert_has_element_new :
forall l : hset, forall e : element_t,
find l (witness e) = 0 -> position (insert l e) (New_Max.new l) > 0.
intros l e Hfind; unfold position; rewrite (hinsert_is_insert l e Hfind);
apply insert_has_element_new.
Qed.

Lemma insert_has_element_rev :
forall l : hset, forall e : element_t, forall cun : cursor,
find l (witness e) = 0 -> position l cun > 0 ->
position (insert l e) cun > 0.
intros l e cun Hfind; unfold position;
rewrite (hinsert_is_insert l e Hfind);
apply insert_has_element_rev.
Qed.

Lemma insert_length :
forall (l : hset), forall (e : element_t),
find l (witness e) = 0 -> length (insert l e) = length l + 1.
intros l e Hfind;  unfold length; rewrite (hinsert_is_insert l e Hfind);
apply insert_length.
Qed.

Lemma insert_element_old :
forall l : hset, forall e : element_t, forall cun : cursor,
find l (witness e) = 0 ->
position l cun > 0 -> element l cun = element (insert l e) cun.
intros l e cun Hfind; unfold element;
rewrite (hinsert_is_insert l e Hfind);
apply insert_element_old.
Qed.

Lemma insert_element_new :
forall l : hset, forall e : element_t,
find l (witness e) = 0 -> element (insert l e) (New_Max.new l) = e.
intros l e Hfind; unfold element; rewrite (hinsert_is_insert l e Hfind);
apply insert_element_new; reflexivity.
Qed.

Lemma insert_find :
forall l : hset, forall w : R, forall e : element_t,
find l (witness e) = 0 -> w <> witness e ->
find l w = find (insert l e) w.
intros l w e Hfind; unfold find; rewrite (hinsert_is_insert l e Hfind);
apply insert_find.
Qed.

Lemma insert_find_new :
forall l : hset, forall e : element_t,
find l (witness e) = 0 ->
find (insert l e) (witness e) = New_Max.new l.
intros l e Hfind; unfold find; rewrite (hinsert_is_insert l e Hfind);
apply insert_find_new; exact Hfind.
Qed.

End Ins.

(*** DELETE ***)

Module Type Delete.
Parameter delete : hset -> cursor -> hset.

Axiom delete_position :
forall l : hset, forall cu cun : cursor,
position l cu > 0 ->
position l cun > 0 -> cu <> cun -> position (delete l cu) cun > 0.
Axiom delete_position_deleted :
forall l : hset, forall cu : cursor,
position l cu > 0 -> position (delete l cu) cu = 0.
Axiom delete_position_inv :
forall l : hset, forall cu cun : cursor,
position l cu > 0 ->
position (delete l cu) cun > 0 -> position l cun > 0.

Axiom delete_length :
forall (l : hset), forall (cu : cursor),
position l cu > 0 ->
length l = 1 + length (delete l cu).

Axiom delete_element :
forall l : hset, forall cu cun : cursor,
position l cu > 0 -> position l cun > 0 -> cun <> cu ->
element (delete l cu) cun = element l cun.

Axiom delete_find :
forall l : hset, forall w : R, forall cu : cursor,
position l cu > 0 -> w <> witness (element l cu) ->
find (delete l cu) w = find l w.
Axiom delete_find_deleted :
forall l : hset, forall cu : cursor,
has_element l cu = true ->
find (delete l cu) (witness(element l cu)) = O.

End Delete.

Module Del : Delete.

Definition delete (m : hset) (cu : cursor) : hset :=
Build_hset (delete m cu) (WFh_delete1 m cu (wf(hthis m)) (hwf m)).

Lemma delete_position :
forall l : hset, forall cu cun : cursor,
position l cu > 0 ->
position l cun > 0 -> cu <> cun -> position (delete l cu) cun > 0.
intros [[l Hwf] Hh] cu cun _; unfold delete; unfold delete1;
unfold position; simpl; clear; generalize 1 (gt_Sn_O O).
induction l; simpl.
intros _ _ Hko; contradict Hko; apply gt_irrefl.
case_eq (beq_nat (fst a) cu); simpl.
case_eq (beq_nat (fst a) cun); [intros Heq1 Heq2 n _ _ Hdiff;
apply beq_nat_true in Heq1; apply beq_nat_true in Heq2; contradict Hdiff;
rewrite <- Heq2; exact Heq1|].
intros _ _ n Hn Hhe _; apply has_element_position1 in Hhe.
apply le_gt_trans with n; [apply position1_has_element; exact Hhe
|exact Hn].
intros _; case (beq_nat (fst a) cun).
intros n Hn _ _; exact Hn.
intros n _; apply (IHl _ (gt_Sn_O n)).
Qed.

Lemma delete_position_deleted :
forall l : hset, forall cu : cursor,
position l cu > 0 -> position (delete l cu) cu = 0.
intros l cu; apply delete_position_deleted.
Qed.

Lemma delete_position_inv :
forall l : hset, forall cu cun : cursor,
position l cu > 0 ->
position (delete l cu) cun > 0 -> position l cun > 0.
intros [[l Hwf] Hh] cu cun; unfold delete; unfold delete1;
unfold position; simpl; clear; generalize 1.
induction l; simpl.
intros n Hko; contradict Hko; apply gt_irrefl.
intros n; case (beq_nat (fst a) cu); simpl;
case (beq_nat (fst a) cun); simpl.
intros Hn _; exact Hn.
intros _ Hhe; apply has_element_position1 in Hhe;
apply (le_gt_trans _ _ _ (position1_has_element l cun (S n) Hhe)
(gt_Sn_O n)).
intros _ Hn; exact Hn.
apply IHl.
Qed.

Lemma delete_length :
forall (l : hset), forall (cu : cursor),
position l cu > 0 ->
length l = 1 + length (delete l cu).
intros [l Hh] cu; unfold delete; apply delete_length.
Qed.

Lemma delete_element :
forall l : hset, forall cu cun : cursor,
position l cu > 0 -> position l cun > 0 -> cun <> cu ->
element (delete l cu) cun = element l cun.
intros [l Hh] cu cun Hcu _; unfold delete; simpl; apply delete_element.
exact Hcu.
Qed.

Lemma delete_find :
forall l : hset, forall w : R, forall cu : cursor,
position l cu > 0 -> w <> witness (element l cu) ->
find (delete l cu) w = find l w.
intros [l Hh] cu cun Hcu; apply delete_find.
apply has_element_position; exact Hcu.
Qed.

Lemma delete_find_deleted :
forall l : hset, forall cu : cursor,
has_element l cu = true ->
find (delete l cu) (witness(element l cu)) = O.
intros [l Hh] cu Hhe; unfold delete; simpl; apply delete1_find_deleted;
[exact Hhe|exact (wf l)|exact Hh].
Qed.

End Del.

(*** REPLACE ***)

Lemma WFh_replace1 :
forall l : Rlist, forall e : element_t,
well_formed l -> well_formed_hashed l ->
well_formed_hashed (replace1 l (find l (witness e)) e).
intros l e; induction l; simpl.
auto.
case_eq (O.eq_real_bool (witness (snd a)) (witness e)).
rewrite <- beq_nat_refl; simpl.
intro Heq; apply beq_real_true in Heq; rewrite Heq; auto.
case_eq(beq_nat (fst a) (find l (witness e))); simpl.
intros Hko _ [Hfst[Hhea _]]; apply beq_nat_true in Hko;
destruct(find_has_element l (witness e)) as [Hhef|Hnil].
contradict Hhea; rewrite Hko; rewrite Hhef;
apply Bool.diff_true_false.
contradict Hfst; rewrite Hko; rewrite Hnil;
apply gt_irrefl.
intros _ _ [_[_ Hwf]] [Hfind Hh].
split; [|apply (IHl Hwf Hh)].
case_eq (O.eq_real_bool (witness (snd a)) (witness e)).
intro Heq; apply beq_real_true in Heq; rewrite <- Heq;
rewrite Hfind; rewrite <- Hfind at 2.
generalize Hwf; clear; induction l; simpl.
reflexivity.
case_eq (beq_nat (fst a0) 0); simpl.
intros Heq [Hko]; contradict Hko; apply beq_nat_true in Heq;
rewrite Heq; apply gt_irrefl.
intros _; case (O.eq_real_bool (witness (snd a0)) (witness (snd a))).
reflexivity.
intros [_[_ Hwf]]; apply (IHl Hwf).
intro Hdiff; apply beq_real_false in Hdiff; 
rewrite <- Hfind; apply (replace1_find l _ _ Hwf Hdiff).
Qed.

Definition hreplace (m : hset) (e : element_t) : hset :=
Build_hset (replace m (find m (witness e)) e)
(WFh_replace1 m e (wf(hthis m)) (hwf m)).

(*** INCLUDE ***)

Definition hinclude (m : hset) (e : element_t) : hset :=
if (beq_nat (find m (witness e)) O) then
Ins.insert m e else hreplace m e.

(*** EXCLUDE ***)

Definition hexclude (m : hset) (cu : cursor) : hset :=
if (beq_nat cu O) then
m else Del.delete m cu.

(*** INTER ***)

Lemma WFh_inter :
forall l1 l2 : list,
well_formed_hashed l1 -> well_formed_hashed (inter l1 l2).
intros [l1 Hwf1] [l2 Hwf2]; unfold inter; simpl.
generalize Hwf1; clear; induction l1; simpl.
auto.
case (beq_nat (find l2 (witness (snd a))) 0); simpl.
intros [_[_ Hwf1]] [_ Hh1]; apply (IHl1 Hwf1 Hh1).
intros [_[_ Hwf1]] [Hfind Hh1]; split; [|apply (IHl1 Hwf1 Hh1)].
generalize Hwf1 Hfind; clear; induction l1; simpl.
reflexivity.
case (beq_nat (find l2 (witness (snd a0))) 0); simpl;
case (O.eq_real_bool (witness (snd a0)) (witness (snd a))); simpl.
intros [Hko _] Heq; contradict Hko; rewrite Heq; apply gt_irrefl.
intros [_[_]]; apply IHl1.
intros _ Hex; exact Hex.
intros [_[_]]; apply IHl1.
Qed.

Definition hinter (l1 l2 : hset) : hset :=
Build_hset (inter l1 l2) (WFh_inter l1 l2 (hwf l1)).

(*** UNION ***)

Lemma WFh_union :
forall l1 l2 : list,
well_formed_hashed l1 -> well_formed_hashed l2 ->
well_formed_hashed (union1 l1 l2 (fun l _ => first1 l)).
intros [l1 Hwf1] [l2 Hwf2]; simpl;
generalize l2 Hwf1 Hwf2; clear; induction l1; simpl.
auto.
intro l2; case_eq (beq_nat (find l2 (witness (snd a))) 0); simpl.
intros Hfind [_[_ Hwf1]] Hwf2 [_ Hh1] Hh2;
generalize (WFh_insert1 l2 (snd a) (New_Max.new l2) Hwf2 Hh2);
rewrite Hfind.
apply (IHl1 _ Hwf1 (WF_insert _ _ _ Hwf2) Hh1).
intros _ [_[_ Hwf1]] Hwf2 [_ Hh1] Hh2;
apply (IHl1 _ Hwf1 Hwf2 Hh1 Hh2).
Qed.

Definition hunionl (l1 l2 : list) : list :=
Build_list (union1 l1 l2 (fun l _ => first1 l))
(WF_union1 (fun l _ => first1 l) l1 l2 (wf l2)).

Definition hunion (l1 l2 : hset) : hset :=
Build_hset (hunionl l1 l2) (WFh_union l1 l2 (hwf l1) (hwf l2)).

Lemma hunion_length :
forall l1 l2 : hset,
length (hunion l1 l2) + length (hinter l1 l2)
= length l1 + length l2.
intros [[l1 Hwf1] Hh1] [[l2 Hwf2] Hh2]; unfold hunion;
unfold hunionl; unfold inter; unfold length; simpl; simpl in Hh1.
apply (union1_length _ _ _ Hwf1 Hh1).
Qed.

Lemma hunion_contains :
forall l1 l2 : hset, forall w : R,
has_element l1 (find l1 w) = true \/
has_element l2 (find l2 w) = true ->
has_element (hunion l1 l2) (find (hunion l1 l2) w) = true.
intros [[l1 Hwf1] Hh1] [[l2 Hwf2] Hh2] w; unfold hunion;
unfold hunionl; unfold inter; unfold length; simpl.
apply (union1_contains _ _ _ _ Hwf1 Hwf2).
Qed.

Lemma hunion_contains_inv :
forall l1 l2 : hset, forall w : R,
has_element (hunion l1 l2) (find (hunion l1 l2) w) = true ->
has_element l1 (find l1 w) = true \/
has_element l2 (find l2 w) = true.
intros [[l1 Hwf1] Hh1] [[l2 Hwf2] Hh2] w; unfold hunion;
unfold hunionl; unfold inter; unfold length; simpl.
apply (union1_contains_inv _ _ _ _ Hwf1 Hwf2).
Qed.

(*** DIFF ***)

Lemma WFh_diff :
forall l1 l2 : list,
well_formed_hashed l1 -> well_formed_hashed (diff l1 l2).
intros [l1 Hwf1] [l2 Hwf2]; unfold inter; simpl.
generalize l1 Hwf1; clear; induction l2; simpl.
auto.
intro l1; case (beq_nat (find l1 (witness (snd a))) 0); simpl.
apply IHl2.
intros Hwf1 Hh1; apply (IHl2 _ (WF_delete1 _ _ Hwf1)).
apply (WFh_delete1 l1 _ Hwf1 Hh1).
Qed.

Definition hdiff (l1 l2 : hset) : hset :=
Build_hset (diff l1 l2) (WFh_diff l1 l2 (hwf l1)).

(*** REPLACE_ELT ***)

Lemma WFh_replace_elt1 :
forall l : Rlist, well_formed l ->
forall e : element_t, forall cu : cursor,
(find l (witness e) = 0 \/ find l (witness e) = cu) ->
well_formed_hashed l ->
well_formed_hashed (replace_elt1 (fun l _ => first1 l) l cu e).
intros l H e cu; unfold replace_elt1; simpl.
case_eq (has_element l cu); [|intros _ _ Hex; exact Hex].
intros Hhe Hfind Hh; assert (find (delete1 l cu) (witness e) = 0).
destruct Hfind as [Hfind|Hfind].
case_eq (O.eq_real_bool (witness e) (witness(element1 l cu))).
intro Heq; apply beq_real_true in Heq;
rewrite Heq; apply (delete1_find_deleted l cu Hhe H Hh).
intro Hdiff; apply beq_real_false in Hdiff;
rewrite (delete1_find l _ cu Hhe Hdiff); exact Hfind.
rewrite <- Hfind in Hhe;
rewrite <- (find_element1 l (witness e) 1 (gt_Sn_O O) H
(position1_has_element _ _ _ Hhe)).
rewrite Hfind; rewrite Hfind in Hhe;
apply (delete1_find_deleted l cu Hhe H Hh).
generalize (first1 l) (delete1 l cu) (WF_delete1 l cu H)
(WFh_delete1 l cu H Hh) H0; clear;
induction r; simpl.
auto.
case (beq_nat (fst a) c); simpl.
intros _ H1 H2; split; [exact H2|exact H1].
case_eq (O.eq_real_bool (witness (snd a)) (witness e)).
intros _ [Hko _] _ Heq; contradict Hko; rewrite Heq; apply gt_irrefl.
intros Hdiff [_[_ Hwf]] [Hfinda Hh] Hfinde; split;
[|apply (IHr Hwf Hh Hfinde)].
rewrite <- insert1_find; [exact Hfinda|apply (beq_real_false _ _ Hdiff)].
Qed.

Definition hreplace_eltl (l : list) (cu : cursor)
(e : element_t) : list :=
if (orb (beq_nat (find l (witness e)) 0)
(beq_nat (find l (witness e)) cu))
then Build_list (replace_elt1 (fun l _ => first1 l) l cu e)
(WF_replace_elt1 (fun l _ => first1 l) l cu e (wf l)) else l.

Lemma WFh_replace_elt : forall l : list, forall cu : cursor,
forall e : element_t,
well_formed_hashed l ->
well_formed_hashed (hreplace_eltl l cu e).
intros [l H] cu e; unfold hreplace_eltl; simpl.
case_eq ((beq_nat (find l (witness e)) 0 ||
beq_nat (find l (witness e)) cu)%bool); simpl.
intros Hfind; unfold replace_elt1; apply Bool.orb_true_elim in Hfind.
destruct Hfind as [Hfind|Hfind]; apply beq_nat_true in Hfind;
apply (WFh_replace_elt1 l H); [left|right]; exact Hfind.
intros _ Hex; exact Hex.
Qed.

Lemma hreplace_eltl_length :
forall l : list, forall cu : cursor, forall e : element_t,
length l = length (hreplace_eltl l cu e).
intros [l Hwf] cu e; unfold hreplace_eltl; unfold length; simpl.
case ((beq_nat (find l (witness e)) 0 ||
beq_nat (find l (witness e)) cu)%bool); [simpl|reflexivity].
apply (replace_elt1_length _ l cu e).
Qed.

Lemma hreplace_eltl_has_element :
forall l : list, forall cu cun : cursor, forall e : element_t,
has_element l cun = has_element (hreplace_eltl l cu e) cun.
intros [l Hwf] cu cun e; unfold hreplace_eltl; simpl.
case ((beq_nat (find l (witness e)) 0 ||
beq_nat (find l (witness e)) cu)%bool); [simpl|reflexivity].
apply (replace_elt1_has_element _ l cu cun e Hwf).
Qed.

Lemma hreplace_eltl_element :
forall l : list, forall cu cun : cursor, forall e : element_t,
cu <> cun -> has_element l cun = true ->
element l cun = element (hreplace_eltl l cu e) cun.
intros [l Hwf] cu cun e; unfold hreplace_eltl; unfold element; simpl.
case ((beq_nat (find l (witness e)) 0 ||
beq_nat (find l (witness e)) cu)%bool); [simpl|reflexivity].
apply (replace_elt1_element1 _ l cu cun e Hwf).
Qed.

Lemma hreplace_eltl_element_replaced :
forall l : list, forall cu : cursor, forall e : element_t,
find l (witness e) = 0 \/ find l (witness e) = cu ->
has_element l cu = true ->
element1 (hreplace_eltl l cu e) cu = e.
intros [l Hwf] cu e; unfold hreplace_eltl; unfold element; simpl.
case_eq ((beq_nat (find l (witness e)) 0 ||
beq_nat (find l (witness e)) cu)%bool); [intros _ _; simpl|intro Hko].
apply (replace_elt1_element1_replaced _ l cu e Hwf).
apply Bool.orb_false_elim in Hko; destruct Hko as [Hko1 Hko2];
intros [Hfind|Hfind]; [contradict Hko1|contradict Hko2];
rewrite Hfind; rewrite <- beq_nat_refl; apply Bool.diff_true_false.
Qed.

Lemma hreplace_eltl_find :
forall l : list, forall cu : cursor, forall e : element_t,
forall w : R, well_formed_hashed l ->
 witness e <> w -> find l w <> cu ->
find l w = find (hreplace_eltl l cu e) w.
intros [l Hwf] cu e w; unfold hreplace_eltl; simpl.
case ((beq_nat (find l (witness e)) 0 ||
beq_nat (find l (witness e)) cu)%bool); [simpl|reflexivity].
apply (replace_elt1_find _ l _ _ _ Hwf).
Qed.

Lemma hreplace_eltl_find_replaced :
forall l : list, forall cu : cursor, forall e : element_t,
well_formed_hashed l -> has_element l cu = true ->
find l (witness e) = 0 \/ find l (witness e) = cu ->
find (hreplace_eltl l cu e) (witness e) = cu.
intros [l Hwf] cu e; unfold hreplace_eltl; simpl.
case_eq ((beq_nat (find l (witness e)) 0 ||
beq_nat (find l (witness e)) cu)%bool); [intros _; simpl|intro Hko].
apply (replace_elt1_find_replaced _ l _ _ Hwf).
apply Bool.orb_false_elim in Hko; destruct Hko as [Hko1 Hko2];
intros _ _ [Hfind|Hfind]; [contradict Hko1|contradict Hko2];
rewrite Hfind; rewrite <- beq_nat_refl; apply Bool.diff_true_false.
Qed.

Definition hreplace_elt (m : hset) (cu : cursor) (e : element_t) : hset :=
Build_hset (hreplace_eltl m cu e) (WFh_replace_elt m cu e (hwf m)).

(***** SPECIFIC TO ORDERED *****)

(*** WELL_FORMED ***)

Fixpoint inf (l : Rlist) (w : R) : Prop :=
match l with
nil => True
| a :: ls => Rgt (witness (snd a)) w /\ inf ls w
end.

Fixpoint well_formed_ordered (l : Rlist) : Prop :=
match l with
nil => True
| a :: ls => inf ls (witness (snd a))
/\ well_formed_ordered ls
end.

Lemma ordered_hashed :
forall l : Rlist,
well_formed_ordered l ->
well_formed_hashed l.
intro l; induction l; simpl.
auto.
intros [Hs Hwf]; split.
generalize Hs; clear; induction l; simpl.
reflexivity.
intros [Hww Hsup];
case_eq (O.eq_real_bool (witness (snd a0)) (witness (snd a))).
intro Hko; apply beq_real_true in Hko.
contradict Hww; rewrite Hko; apply Rgt_irrefl.
intros _; apply(IHl Hsup).
apply (IHl Hwf).
Qed.

(*** MAP ***)

Record oset := {othis :> list; owf : well_formed_ordered othis}.

Definition to_hashed (m : oset) :=
Build_hset (othis m) (ordered_hashed (othis m) (owf m)).

(***** FUNCTIONS RETURNING MAPS *****)

(*** EMPTY ***)

Lemma WF_onil : well_formed_ordered nil.
simpl.
auto.
Qed.

Definition oempty : oset :=
Build_oset empty WF_onil.

(*** LEFT ***)

Lemma left1_ordered :
forall l : Rlist, forall cu : cursor,
well_formed_ordered l -> well_formed_ordered (left1 l cu).
intros l cu; induction l; simpl.
auto.
case (beq_nat (fst a) cu); simpl.
auto.
intros [Hinf Hwf]; split; [|apply(IHl Hwf)].
generalize Hinf; clear; induction l; simpl.
auto.
case(beq_nat (fst a0) cu); simpl.
auto.
intros [Hw Hinf]; split; [exact Hw|apply(IHl Hinf)].
Qed.

Lemma WF_oleft :
forall l : list, forall cu : cursor,
well_formed_ordered l -> well_formed_ordered (left l cu).
intros [l H] cu; unfold left; case (beq_nat cu 0); simpl.
auto.
apply left1_ordered.
Qed.

Definition oleft (m : oset) (cu : cursor) : oset :=
if beq_nat cu 0 then m
else Build_oset (left m cu) (WF_oleft m cu (owf m)).

(*** RIGHT ***)

Lemma right1_ordered :
forall l : Rlist, forall cu : cursor,
well_formed_ordered l -> well_formed_ordered (right1 l cu).
intros l cu; induction l; simpl.
auto.
case (beq_nat (fst a) cu); simpl.
auto.
intros [_ Hwf]; apply(IHl Hwf).
Qed.

Lemma WF_oright :
forall l : list, forall cu : cursor,
well_formed_ordered l -> well_formed_ordered (right l cu).
intros [l H] cu; unfold right; case (beq_nat cu 0); simpl.
auto.
apply right1_ordered.
Qed.

Definition oright (m : oset) (cu : cursor) : oset :=
if beq_nat cu 0 then oempty
else Build_oset (right m cu) (WF_oright m cu (owf m)).

(*** ORDER ***)

Lemma po1_el1_order :
forall l : Rlist, well_formed l -> well_formed_ordered l ->
forall cu1 cu2 : cursor, forall n : nat,
position1 l cu1 n > 0 -> position1 l cu2 n > 0 ->
position1 l cu2 n > position1 l cu1 n ->
Rgt (witness (element1 l cu2)) (witness (element1 l cu1)).
intros l Hwf Hmap cu1 cu2; induction l; simpl.
intros _ Hko; contradict Hko; apply gt_irrefl.
simpl in Hmap; simpl in Hwf; destruct Hwf as [_[_ Hwf]];
destruct Hmap as [Hsup Hmap].
case(beq_nat (fst a) cu2);
case(beq_nat (fst a) cu1).
intros n _ _ Hko; contradict Hko; apply gt_irrefl.
intros n Hpos _ Hko;
apply (has_element_position1 l) in Hpos.
apply (position1_has_element l _ (S n)) in Hpos.
contradict Hko; apply le_not_gt.
apply (le_trans _ (S n) _ (le_n_Sn n) Hpos).
intros n _ Hpos _; generalize n Hsup Hpos; clear.
induction l; simpl.
intros _ _ Hko; contradict Hko; apply gt_irrefl.
case(beq_nat (fst a0) cu2).
intros n [Hr _] _; exact Hr.
intros n [_ Hinf] Hpos; apply (IHl (S n) Hinf Hpos).
intros n; apply (IHl Hwf Hmap).
Qed.

Lemma po_el_order :
forall m : oset, forall cu1 cu2 : cursor,
position m cu1 > 0 -> position m cu2 > 0 ->
position m cu2 > position m cu1 ->
Rgt (witness (element m cu2)) (witness (element m cu1)).
intros [[l Hwf] Hmap] cu1 cu2;
apply (po1_el1_order l Hwf Hmap).
Qed.

Lemma el1_po1_order :
forall l : Rlist, well_formed l -> well_formed_ordered l ->
forall cu1 cu2 : cursor, forall n : nat,
position1 l cu1 n > 0 -> position1 l cu2 n > 0 ->
Rgt (witness (element1 l cu2)) (witness (element1 l cu1)) ->
position1 l cu2 n > position1 l cu1 n.
intros l Hwf Hmap cu1 cu2; induction l; simpl.
intros _ Hko; contradict Hko; apply gt_irrefl.
simpl in Hmap; simpl in Hwf; destruct Hwf as [_[_ Hwf]];
destruct Hmap as [Hsup Hmap].
case(beq_nat (fst a) cu2);
case(beq_nat (fst a) cu1).
intros n _ _ Hko; contradict Hko; apply Rgt_irrefl.
intros n Hpos _ Hko; contradict Hko; apply Rge_not_gt;
apply Rgt_ge.
generalize n Hsup Hpos; clear.
induction l; simpl.
intros _ _ Hko; contradict Hko; apply gt_irrefl.
case(beq_nat (fst a0) cu1).
intros n [Hr _] _; exact Hr.
intros n [_ Hinf] Hpos; apply (IHl (S n) Hinf Hpos).
intros n _ Hpos _; apply le_S_gt.
apply (position1_has_element l).
apply (has_element_position1 l _ _ Hpos).
intros n; apply (IHl Hwf Hmap).
Qed.

Lemma el_po_order :
forall m : oset, forall cu1 cu2 : cursor,
position m cu1 > 0 -> position m cu2 > 0 ->
Rgt (witness (element m cu2)) (witness (element m cu1)) ->
position m cu2 > position m cu1.
intros [[l Hwf] Hmap] cu1 cu2;
apply (el1_po1_order l Hwf Hmap).
Qed.

Lemma w_po_order_l :
forall m : oset, forall cu1 : cursor, forall w2 : R,
position m cu1 > 0 ->
position m (find m w2) > 0 ->
Rgt w2 (witness (element m cu1)) ->
position m (find m w2) > position m cu1.
intros m cu11 w2; simpl.
intros Hp1 Hp2 Hw;
apply (el_po_order m _ _ Hp1 Hp2).
rewrite (find_element m _ Hp2).
exact Hw.
Qed.

Lemma w_po_order_r :
forall m : oset, forall cu1 : cursor, forall w2 : R,
position m cu1 > 0 ->
position m (find m w2) > 0 ->
Rgt (witness (element m cu1)) w2 ->
position m cu1 > position m (find m w2).
intros m cu11 w2; simpl.
intros Hp1 Hp2 Hw;
apply (el_po_order m _ _ Hp2 Hp1).
rewrite (find_element m _ Hp2).
exact Hw.
Qed.

(*** CEILING ***)

Fixpoint ceiling (l : Rlist) (w : R) : cursor :=
match l with
nil => 0
| a :: ls => if O.gt_real_bool w (witness (snd a)) then
 ceiling ls w else (fst a)
end.

Lemma ceiling_position1 :
forall l : Rlist, forall w : R, forall n : nat, n > 0 ->
ceiling l w = 0 \/ position1 l (ceiling l w) n > 0.
intros l w; induction l; simpl.
intros n _; left; reflexivity.
intros n Hn; case (O.gt_real_bool w (witness (snd a))); simpl.
destruct (IHl (S n) (gt_Sn_O n)) as [Hc | Hp].
left; exact Hc.
case (beq_nat (fst a) (ceiling l w)); right;
[apply Hn|apply Hp].
rewrite <- beq_nat_refl; right; exact Hn.
Qed.

Lemma ceiling_position :
forall l : list, forall w : R,
ceiling l w = 0 \/ position l (ceiling l w) > 0.
intros l w; apply ceiling_position1; apply gt_Sn_O.
Qed.

Lemma ceiling_O :
forall l : oset, forall w : R,
ceiling l w = 0 ->
length l = 0 \/ Rgt w (witness (element l (last l))).
unfold length; unfold element; unfold last;
intros [[l Hwf]Ho] w; simpl; induction l; simpl.
intros _; left; reflexivity.
simpl in Ho; destruct Ho as [Hw Ho];
simpl in Hwf; destruct Hwf as [Hfst[_ Hwf]].
case_eq (O.gt_real_bool w (witness (snd a))).
intros Hf Hc; right;
apply gtb_real_complete in Hf.
destruct (IHl Hwf Ho Hc) as [Hl | Hsup].
generalize Hl Hw Hf; clear; case l; simpl.
rewrite <- beq_nat_refl.
intros _ _ Hw; exact Hw.
intros aa ll Hko; symmetry in Hko; contradict Hko; apply O_S.
case_eq l.
simpl; intros _; rewrite <- beq_nat_refl; apply Hf.
intros aa ll Hal.
rewrite <- Hal; case(beq_nat (fst a) (last1 l));
[exact Hf | exact Hsup].
intros _ Hko; rewrite Hko in Hfst; contradict Hfst;
apply gt_irrefl.
Qed.

Lemma ceiling_base1 :
forall l : Rlist, well_formed l -> forall w : R, forall n : nat,
position1 l (ceiling l w) n > 0 ->
Rle w (witness (element1 l (ceiling l w))).
intros l Hwf w; induction l; simpl.
intros _ Hko; contradict Hko; apply gt_irrefl.
simpl in Hwf; destruct Hwf as [Hfst[Hhe Hwf]].
case_eq (O.gt_real_bool w (witness (snd a))); intro Hgt.
apply gtb_real_complete in Hgt.
case_eq (beq_nat (fst a) (ceiling l w)); intro Heq.
apply beq_nat_true in Heq;
destruct (ceiling_position1 l w 1 (gt_Sn_O O)) as [Hko|Hko].
rewrite Hko in Heq; rewrite Heq in Hfst; contradict Hfst;
apply gt_irrefl.
rewrite <- Heq in Hko;
apply (has_element_position1 l) in Hko.
rewrite Hhe in Hko; contradict Hko; apply Bool.diff_false_true.
intro n; apply (IHl Hwf).
rewrite <- beq_nat_refl.
intros n _; apply gtb_real_complete_conv in Hgt;
apply Hgt.
Qed.

Lemma ceiling_base :
forall l : list, forall w : R,
position l (ceiling l w) > 0 ->
Rle w (witness (element l (ceiling l w))).
intros [l Hwf] w; apply ceiling_base1.
simpl; apply Hwf.
Qed.

Lemma ceiling_find :
forall l : oset,
forall w : R,
Rgt (witness (element1 l (ceiling l w))) w ->
find l w = 0.
intros [[l Hwf]Ho] w; simpl;
simpl in Ho; induction l; simpl.
reflexivity.
simpl in Ho; destruct Ho as [Hinf Ho].
case_eq(O.gt_real_bool w (witness (snd a)));
intro Hgt; [apply gtb_real_complete in Hgt|
apply gtb_real_complete_conv in Hgt].
case_eq(O.eq_real_bool (witness (snd a)) w);
intro Heq; [apply beq_real_true in Heq; rewrite Heq in Hgt;
contradict Hgt; apply Rgt_irrefl|].
simpl in Hwf; destruct Hwf as [Hfst[Hhe Hwf]];
case_eq (beq_nat (fst a) (ceiling l w)).
intros Hko; apply beq_nat_true in Hko;
destruct (ceiling_position1 l w 1 (gt_Sn_O O)).
rewrite H in Hko; rewrite Hko in Hfst; contradict Hfst;
apply gt_irrefl.
rewrite <- Hko in H;
apply(has_element_position1 l) in H.
contradict Hhe; rewrite H; apply Bool.diff_true_false.
intros _; apply (IHl Hwf Ho).
rewrite <- beq_nat_refl; clear Hgt; intro Hgt.
case_eq (O.eq_real_bool (witness (snd a)) w);
[intro Heq; apply beq_real_true in Heq; contradict Hgt;
rewrite Heq; apply Rgt_irrefl|intros _].
generalize Hinf Hgt; clear; induction l; simpl.
reflexivity.
intros [Hgt2 Hinf] Hgt1; case_eq(O.eq_real_bool (witness (snd a0)) w).
intro Hko; apply beq_real_true in Hko;
apply (Rgt_trans _ _ _ Hgt2) in Hgt1.
contradict Hgt1; rewrite Hko; apply Rgt_irrefl.
intros _; apply(IHl Hinf Hgt1).
Qed.

Lemma ceiling_left1 :
forall m : Rlist, well_formed m -> well_formed_ordered m ->
forall w : R,
Rgt (witness (element1 m (ceiling m w))) w ->
ceiling m w <> first1 m ->
Rgt w (witness(element1 m (last1 (left1 m (ceiling m w))))).
intros l Hwf Ho w; induction l; simpl.
intros _ Hko; contradict Hko; reflexivity.
simpl in Ho; destruct Ho as [Hw Ho];
simpl in Hwf; destruct Hwf as [Hfst[Hhe Hwf]].
case_eq (O.gt_real_bool w (witness (snd a))); simpl.
case_eq (beq_nat (fst a) (ceiling l w)); simpl; [intros Heq _ _ Hko;
contradict Hko; symmetry; apply (beq_nat_true _ _ Heq)|].
case_eq (left1 l (ceiling l w)).
rewrite <- beq_nat_refl.
intros _ _ Hgt _ _; apply gtb_real_complete in Hgt; apply Hgt.
intros aa ll Haall; rewrite <- Haall;
case_eq (beq_nat (fst a) (last1 (left1 l (ceiling l w)))).
intros Heq _ _ _ _; apply beq_nat_true in Heq.
contradict Heq; generalize Hhe Hfst; clear; induction l; simpl.
intros _ Hko Heq; contradict Hko; rewrite Heq; apply gt_irrefl.
intros Hor Hs; apply Bool.orb_false_elim in Hor;
destruct Hor as [Hd Hhe].
case (O.gt_real_bool w (witness (snd a0))).
case (beq_nat (fst a0) (ceiling l w)); simpl.
intros Heq; contradict Hs; rewrite Heq; apply gt_irrefl.
case_eq (left1 l (ceiling l w)).
intros _ Heq; symmetry in Heq; contradict Hd; rewrite Heq;
rewrite <- beq_nat_refl; apply Bool.diff_true_false.
intros p l0 Hleft; rewrite <- Hleft; apply (IHl Hhe Hs).
rewrite <- beq_nat_refl; simpl; intro Heq; contradict Hs;
rewrite Heq; apply gt_irrefl.
intros _ _ _ Hgt _.
case_eq (beq_nat (ceiling l w) (first1 l)); intro Heq;
[apply beq_nat_true in Heq; rewrite Heq|
apply beq_nat_false in Heq; apply(IHl Hwf Ho Hgt Heq)].
assert (nil <> left1 l (ceiling l w)).
rewrite Haall; apply nil_cons.
rewrite Heq in Hgt; rewrite Heq in H;
generalize Hw Hgt H; clear; induction l; simpl.
intros _ _ Hko; contradict Hko; reflexivity.
rewrite <- beq_nat_refl; simpl.
intros _ _ Hko; contradict Hko; reflexivity.
intros _ _ Hko; contradict Hko; reflexivity.
Qed.

Lemma ceiling_oleft :
forall m : oset,
forall w : R,
position m (ceiling m w) > 0 ->
Rgt (witness (element m (ceiling m w))) w ->
ceiling m w <> first m ->
Rgt w (witness(element m (last (oleft m (ceiling m w))))).
intros [[l Hwf]Ho] w; unfold oleft; simpl.
case_eq(beq_nat (ceiling l w) 0); simpl.
intro Heq; apply beq_nat_true in Heq; rewrite Heq.
intro Hko; rewrite (position_no_element) in Hko.
contradict Hko; apply gt_irrefl.
unfold element; unfold last; unfold left; simpl;
intros HH _; rewrite HH; apply ceiling_left1;
[exact Hwf|exact Ho].
Qed.

Lemma ceiling_previous1 :
forall l : Rlist, well_formed l -> well_formed_ordered l ->
forall w : R, forall n : nat, forall m : nat,
has_element l m = false ->
position1 l (previous1 l (ceiling l w) m) n > 0 ->
Rgt w (witness(element1 l (previous1 l (ceiling l w) m))).
intros l Hwf Ho w; induction l; simpl.
intros _ _ _ Hko; contradict Hko; apply gt_irrefl.
simpl in Ho; destruct Ho as [Hinf Ho];
simpl in Hwf; destruct Hwf as [Hfst[Hhe Hwf]].
case_eq(O.gt_real_bool w (witness (snd a)));
[|rewrite <- beq_nat_refl].
case_eq(beq_nat (fst a) (ceiling l w)).
intro Hko; apply beq_nat_true in Hko; rewrite Hko in Hhe;
rewrite Hko in Hfst.
destruct (ceiling_position1 l w 1 (gt_Sn_O O)) as [Heq|Hht].
contradict Hfst; rewrite Heq; apply gt_irrefl.
contradict Hhe; rewrite(has_element_position1 l _ 1 Hht).
apply Bool.diff_true_false.
case_eq(beq_nat (fst a) (previous1 l (ceiling l w) (fst a))).
intros _ _ Hgt n m _ _; apply gtb_real_complete in Hgt; exact Hgt.
intros _ _ _ n m _; apply (IHl Hwf Ho _ _ Hhe).
intros Hle n m Horb; apply Bool.orb_false_elim in Horb.
destruct Horb as [Hb Hhm]; rewrite Hb.
intro Hko; apply (has_element_position1 l) in Hko.
contradict Hko; rewrite Hhm; apply Bool.diff_false_true.
Qed.

Lemma ceiling_previous :
forall l : oset,
forall w : R,
position l (previous l (ceiling l w)) > 0 ->
Rgt w (witness(element l (previous l (ceiling l w)))).
intros [[l Hwf] Ho] w; unfold position; unfold element;
unfold previous; simpl.
case_eq(has_element l 0); [|apply (ceiling_previous1 l Hwf Ho)].
intros Hko; apply (position1_has_element l _ 1) in Hko.
rewrite (position1_no_element l Hwf _ (gt_Sn_O O)) in Hko.
contradict Hko; apply le_Sn_O.
Qed.

(*** INSERT ***)

Definition oinsert1 (l : Rlist) (e : element_t) (cu : cursor) : Rlist :=
if (beq_nat (find l (witness e)) 0) then
insert1 l (ceiling l (witness e)) cu e else l.

Lemma WFo_insert1 :
forall l : Rlist, forall e : element_t,
forall cun : cursor,
well_formed l ->
well_formed_ordered l ->
well_formed_ordered (oinsert1 l e cun).
intros l e cun; unfold oinsert1; simpl;
destruct (find_has_element l (witness e)).
case_eq (beq_nat (find l (witness e)) 0).
intros Hko Hwf; apply beq_nat_true in Hko;
apply (position1_has_element l _ 1) in H; contradict H;
rewrite Hko; rewrite (position1_no_element l Hwf 1 (gt_Sn_O O));
apply gt_irrefl.
intros _ Hwf Hr; exact Hr.
rewrite H; rewrite <- beq_nat_refl; generalize H.
clear; induction l; simpl.
auto.
case_eq(O.eq_real_bool (witness (snd a)) (witness e)).
intros _ Heq [Hko]; contradict Hko; rewrite Heq; apply gt_irrefl.
intros Hdiff; apply beq_real_false in Hdiff;
case_eq(O.gt_real_bool (witness e) (witness (snd a))); simpl.
case_eq (beq_nat (fst a) (ceiling l (witness e))); simpl.
intros Heq _ _ [Hfst[Hhe]]; apply beq_nat_true in Heq;
destruct (ceiling_position1 l (witness e) 1 (gt_Sn_O O)) as [Hko | Hko].
contradict Hfst; rewrite Heq; rewrite Hko; apply gt_irrefl.
contradict Hhe; apply has_element_position1 in Hko;
rewrite Heq; rewrite Hko; apply Bool.diff_true_false.
intros _ Hgt Hfind [_[_ Hwf]] [Hinf Ho].
simpl in IHl.
split; [apply gtb_real_complete in Hgt|apply (IHl Hfind Hwf Ho)].
generalize Hinf Hgt Hwf; clear; induction l; simpl.
intros _ Hr; split; [exact Hr|auto].
case_eq(O.gt_real_bool (witness e) (witness (snd a0))); simpl.
case_eq (beq_nat (fst a0) (ceiling l (witness e))); simpl.
intros Heq _ _ _ [Hfst[Hhe]]; apply beq_nat_true in Heq;
destruct (ceiling_position1 l (witness e) 1 (gt_Sn_O O)) as [Hko | Hko].
contradict Hfst; rewrite Heq; rewrite Hko; apply gt_irrefl.
contradict Hhe; apply has_element_position1 in Hko;
rewrite Heq; rewrite Hko; apply Bool.diff_true_false.
intros _ _ [Hgt Hinf] Hgte [_[_ Hwf]]; split.
exact Hgt.
apply (IHl Hinf Hgte Hwf).
rewrite <- beq_nat_refl; simpl.
intros _ HH He _; split.
exact He.
exact HH.
rewrite <- beq_nat_refl; simpl.
intros Hgt _ _ Hwf; apply gtb_real_complete_conv in Hgt.
apply Rle_lt_or_eq_dec in Hgt; destruct Hgt as [Hgt | Hko];
[|contradict Hdiff; rewrite Hko; reflexivity].
apply Rlt_gt in Hgt;
split; [split; [exact Hgt|]| exact Hwf].
destruct Hwf as [HH _]; generalize HH Hgt;
clear; induction l; simpl.
auto.
intros [Ht1 Hinf] Ht2; split;
[apply (Rgt_trans _ _ _ Ht1 Ht2) | apply (IHl Hinf Ht2)].
Qed.

Definition oinsertl (l : list) (e : element_t) : list :=
if (beq_nat (find l (witness e)) 0) then
(insert l (ceiling l (witness e)) e) else l.

Lemma WFo_insert : forall l : list, forall e : element_t,
well_formed_ordered l ->
well_formed_ordered (oinsertl l e).
intros [l H] e; unfold oinsertl; unfold insert; simpl.
intros Ho; apply (WFo_insert1 l e (New_Max.new l) H) in Ho.
generalize Ho; unfold oinsert1.
case (beq_nat (find l (witness e)) 0); simpl;
intro Hr; exact Hr.
Qed.

Lemma oinsertl_is_insert :
forall l : oset, forall e : element_t,
find l (witness e) = 0 ->
oinsertl l e = insert l (ceiling l (witness e)) e.
intros [[l Hwf] Ho] e; unfold oinsertl;
unfold first; simpl.
intro Hfind; assert(find l (witness e) = 0).
clear Ho; generalize Hfind; case l; simpl;
[|intros a ll]; intros Hr; exact Hr.
rewrite H; rewrite <- beq_nat_refl; reflexivity.
Qed.

Lemma oinsertl_position1_inf :
forall l : Rlist, forall e : element_t, forall cu cun : cursor,
has_element l cu = true -> has_element l cun = false ->
well_formed l -> well_formed_ordered l ->
Rgt (witness e) (witness (element1 l cu)) ->
forall n : nat,
position1 (insert1 l (ceiling l (witness e)) cun e) cu n
= position1 l cu n.
intros l e cu cun; induction l; simpl.
intro Hko; contradict Hko; apply Bool.diff_false_true.
case_eq (beq_nat (fst a) cu); simpl.
intros Heq _ _ [Hfst[Hhea Hwf]] [Hinf Ho] Hgt.
apply gtb_real_correct in Hgt.
rewrite Hgt; simpl.
case_eq (beq_nat (fst a) (ceiling l (witness e))).
intro Hko; apply beq_nat_true in Hko;
destruct (ceiling_position1 l (witness e) 1 (gt_Sn_O O)) as [HH | HH].
contradict Hfst; rewrite Hko; rewrite HH; apply gt_irrefl.
apply has_element_position1 in HH; contradict HH;
rewrite <- Hko; rewrite Hhea; apply Bool.diff_false_true.
intros _; apply beq_nat_true in Heq; rewrite <- Heq; simpl.
rewrite <- beq_nat_refl; reflexivity.
case_eq (O.gt_real_bool (witness e) (witness (snd a))); simpl.
case_eq (beq_nat (fst a) (ceiling l (witness e))); simpl.
intros Hko _ _ _ _ [Hfst[Hhea _]]; apply beq_nat_true in Hko;
destruct (ceiling_position1 l (witness e) 1 (gt_Sn_O O)) as [HH | HH].
contradict Hfst; rewrite Hko; rewrite HH; apply gt_irrefl.
apply has_element_position1 in HH; contradict HH;
rewrite <- Hko; rewrite Hhea; apply Bool.diff_false_true.
intros _ _ H; rewrite H; simpl.
intros Hhecu Hint [_[_ Hwf]] [_ Ho] Hgte n;
apply Bool.orb_false_elim in Hint; destruct Hint as [Hneq Hhecun];
apply (IHl Hhecu Hhecun Hwf Ho Hgte).
rewrite <- beq_nat_refl; simpl.
intros Hle _ Hecu _ _ [Hinf _] Hgt; apply gtb_real_complete_conv in Hle.
contradict Hgt; generalize Hle Hecu Hinf; clear; induction l; simpl.
intros _ Hko; contradict Hko; apply Bool.diff_false_true.
case (beq_nat (fst a0) cu).
intros Hle _ [Hgt1 _] Hgt2; contradict Hle; apply Rgt_not_le.
apply (Rgt_trans _ _ _ Hgt2 Hgt1).
rewrite Bool.orb_false_l.
intros Hle Hhe [_ Hinf]; apply (IHl Hle Hhe Hinf).
Qed.

Lemma oinsertl_position_inf :
forall l : list, forall e : element_t, forall cu : cursor,
position l cu > 0 -> well_formed_ordered l ->
Rgt (witness e) (witness (element l cu)) ->
position (insert l (ceiling l (witness e)) e) cu = position l cu.
intros [l Hwf] e cu; unfold position; unfold element; unfold insert;
simpl; intros Hpos Ho Hgt; apply has_element_position1 in Hpos.
apply (oinsertl_position1_inf l e cu _ Hpos (New_Max.new_has_element l)
Hwf Ho Hgt).
Qed.

Lemma oinsertl_position1_sup :
forall l : Rlist, forall e : element_t, forall cu cun : cursor,
has_element l cu = true -> has_element l cun = false ->
well_formed l -> well_formed_ordered l ->
Rgt (witness (element1 l cu)) (witness e) ->
forall n : nat,
position1 (insert1 l (ceiling l (witness e)) cun e) cu n
= S(position1 l cu n).
intros l e cu cun; induction l; simpl.
intro Hko; contradict Hko; apply Bool.diff_false_true.
case_eq (beq_nat (fst a) cu); simpl.
intros Heq _ Hint [Hfst[Hhea Hwf]] [Hinf Ho] Hgt.
apply Bool.orb_false_elim in Hint; destruct Hint as [Hneq _].
apply Rgt_ge in Hgt; apply Rge_le in Hgt;
apply gtb_real_correct_conv in Hgt.
rewrite Hgt; simpl.
rewrite <- beq_nat_refl; simpl.
apply beq_nat_true in Heq; rewrite <- Heq; case_eq (beq_nat cun (fst a)).
intro Hko; apply beq_nat_true in Hko; contradict Hneq;
rewrite Hko; rewrite <- beq_nat_refl; apply Bool.diff_true_false.
rewrite <- beq_nat_refl; reflexivity.
case_eq (O.gt_real_bool (witness e) (witness (snd a))); simpl.
case_eq (beq_nat (fst a) (ceiling l (witness e))); simpl.
intros Hko _ _ _ _ [Hfst[Hhea _]]; apply beq_nat_true in Hko;
destruct (ceiling_position1 l (witness e) 1 (gt_Sn_O O)) as [HH | HH].
contradict Hfst; rewrite Hko; rewrite HH; apply gt_irrefl.
apply has_element_position1 in HH; contradict HH;
rewrite <- Hko; rewrite Hhea; apply Bool.diff_false_true.
intros _ _ H; rewrite H; simpl.
intros Hhecu Hint [_[_ Hwf]] [_ Ho] Hgte n;
apply Bool.orb_false_elim in Hint; destruct Hint as [Hneq Hhecun];
apply (IHl Hhecu Hhecun Hwf Ho Hgte).
rewrite <- beq_nat_refl; simpl.
intros Hle Hacu Hecu Hecun _ [Hinf _] Hgt;
apply Bool.orb_false_elim in Hecun; destruct Hecun as [Hdiff Hecun];
apply gtb_real_complete_conv in Hle.
rewrite Hacu; case_eq (beq_nat cun cu).
intro Hko; apply beq_nat_true in Hko; contradict Hecun; rewrite Hko;
rewrite Hecu; apply Bool.diff_true_false.
intros _ n; apply (plus_reg_l _ _ (S n)).
rewrite <- plus_n_Sm; rewrite <- plus_Sn_m.
rewrite (plus_comm (S n)); rewrite (plus_comm (S (S n))).
apply position1_eq; exact Hecu.
Qed.

Lemma oinsertl_position_sup :
forall l : list, forall e : element_t, forall cu : cursor,
position l cu > 0 -> well_formed_ordered l ->
Rgt (witness (element l cu)) (witness e) ->
position (insert l (ceiling l (witness e)) e) cu = S(position l cu).
intros [l Hwf] e cu; unfold position; unfold element; unfold insert;
simpl; intros Hpos Ho Hgt; apply has_element_position1 in Hpos.
apply (oinsertl_position1_sup l e cu _ Hpos
(New_Max.new_has_element l) Hwf Ho Hgt).
Qed.

Definition oinsert (m : oset) (e : element_t) : oset :=
Build_oset (oinsertl m e) (WFo_insert m e (owf m)).

(*** DELETE ***)

Lemma WFo_delete1 :
forall l : Rlist, forall cu : cursor,
well_formed_ordered l -> well_formed_ordered (delete1 l cu).
intros l cu; induction l; simpl.
auto.
case (beq_nat (fst a) cu); simpl.
intros [_ H]; exact H.
intros [Hf Hwfh]; split; [|apply (IHl Hwfh)].
generalize Hf; clear; induction l; simpl.
auto.
case (beq_nat (fst a0) cu); simpl.
intros [_ He]; exact He.
intros [Hgt Hinf]; split.
exact Hgt.
apply (IHl Hinf).
Qed.

Definition odelete (m : oset) (cu : cursor) : oset :=
Build_oset (delete m cu) (WFo_delete1 m cu (owf m)).

(*** REPLACE ***)

Lemma WFo_replace1 :
forall l : Rlist, forall e : element_t,
well_formed l -> well_formed_ordered l ->
well_formed_ordered (replace1 l (find l (witness e)) e).
intros l e; induction l; simpl.
auto.
case_eq (O.eq_real_bool (witness (snd a)) (witness e)).
rewrite <- beq_nat_refl; simpl.
intro Heq; apply beq_real_true in Heq; rewrite Heq; auto.
case_eq(beq_nat (fst a) (find l (witness e))); simpl.
intros Hko _ [Hfst[Hhea _]]; apply beq_nat_true in Hko;
destruct(find_has_element l (witness e)) as [Hhef|Hnil].
contradict Hhea; rewrite Hko; rewrite Hhef;
apply Bool.diff_true_false.
contradict Hfst; rewrite Hko; rewrite Hnil;
apply gt_irrefl.
intros _ _ [_[_ Hwf]] [Hinf Ho].
split; [|apply (IHl Hwf Ho)].
generalize Hinf Hwf; clear; induction l; simpl.
auto.
case_eq(O.eq_real_bool (witness (snd a0)) (witness e)).
rewrite <- beq_nat_refl; simpl.
intro Heq; apply beq_real_true in Heq; rewrite Heq; auto.
case_eq(beq_nat (fst a0) (find l (witness e))).
intros Hko _ _ [Hfst[Hhea _]]; apply beq_nat_true in Hko;
destruct(find_has_element l (witness e)) as [Hhef|Hnil].
contradict Hhea; rewrite Hko; rewrite Hhef;
apply Bool.diff_true_false.
contradict Hfst; rewrite Hko; rewrite Hnil;
apply gt_irrefl.
intros _ _ [Hgt Hinf] [_[_ Hwf]]; simpl.
split; [exact Hgt|apply(IHl Hinf Hwf)].
Qed.

Definition oreplace (m : oset) (e : element_t) : oset :=
Build_oset (replace m (find m (witness e)) e)
(WFo_replace1 m e (wf(othis m)) (owf m)).

(*** INCLUDE ***)

Definition oinclude (m : oset) (e : element_t) : oset :=
if (beq_nat (find m (witness e)) O) then
oinsert m e else oreplace m e.

(*** EXCLUDE ***)

Definition oexclude (m : oset) (cu : cursor) : oset :=
if (beq_nat cu O) then
m else odelete m cu.

(*** INTER ***)

Lemma WFo_inter :
forall l1 l2 : list,
well_formed_ordered l1 -> well_formed_ordered (inter l1 l2).
intros [l1 Hwf1] [l2 Hwf2]; unfold inter; simpl.
clear; induction l1; simpl.
auto.
case (beq_nat (find l2 (witness (snd a))) 0); simpl.
intros [_ Hh1]; apply (IHl1 Hh1).
intros [Hinf Hh1]; split; [|apply (IHl1 Hh1)].
generalize Hinf; clear; induction l1; simpl.
auto.
case (beq_nat (find l2 (witness (snd a0))) 0); simpl.
intros [_ Hinf]; apply (IHl1 Hinf).
intros [Hgt Hinf]; split; [exact Hgt|exact (IHl1 Hinf)].
Qed.

Definition ointer (l1 l2 : oset) : oset :=
Build_oset (inter l1 l2) (WFo_inter l1 l2 (owf l1)).

(*** UNION ***)

Lemma WFo_union :
forall l1 l2 : list,
well_formed_ordered l1 -> well_formed_ordered l2 ->
well_formed_ordered (union1 l1 l2 (fun l e => ceiling l (witness e))).
intros [l1 Hwf1] [l2 Hwf2]; simpl;
generalize l2 Hwf1 Hwf2; clear; induction l1; simpl.
auto.
intro l2; case_eq (beq_nat (find l2 (witness (snd a))) 0); simpl.
intros Hfind [_[_ Hwf1]] Hwf2 [_ Ho1] Ho2;
generalize (WFo_insert1 l2 (snd a) (New_Max.new l2) Hwf2 Ho2);
unfold oinsert1; rewrite Hfind.
apply (IHl1 _ Hwf1 (WF_insert _ _ _ Hwf2) Ho1).
intros _ [_[_ Hwf1]] Hwf2 [_ Ho1] Ho2;
apply (IHl1 _ Hwf1 Hwf2 Ho1 Ho2).
Qed.

Definition ounionl (l1 l2 : list) : list :=
Build_list (union1 l1 l2 (fun l e => ceiling l (witness e)))
(WF_union1 (fun l e => ceiling l (witness e)) l1 l2 (wf l2)).

Definition ounion (l1 l2 : oset) : oset :=
Build_oset (ounionl l1 l2) (WFo_union l1 l2 (owf l1) (owf l2)).

Lemma ounion_length :
forall l1 l2 : oset,
length (ounion l1 l2) + length (ointer l1 l2)
= length l1 + length l2.
intros [[l1 Hwf1] Ho1] [[l2 Hwf2] Ho2]; unfold hunion;
unfold hunionl; unfold inter; unfold length; simpl; simpl in Ho1.
apply (union1_length _ _ _ Hwf1 (ordered_hashed l1 Ho1)).
Qed.

Lemma ounion_contains :
forall l1 l2 : oset, forall w : R,
has_element l1 (find l1 w) = true \/
has_element l2 (find l2 w) = true ->
has_element (ounion l1 l2) (find (ounion l1 l2) w) = true.
intros [[l1 Hwf1] Ho1] [[l2 Hwf2] Ho2] w; unfold ounion;
unfold ounionl; unfold inter; unfold length; simpl.
apply (union1_contains _ _ _ _ Hwf1 Hwf2).
Qed.

Lemma ounion_contains_inv :
forall l1 l2 : oset, forall w : R,
has_element (ounion l1 l2) (find (ounion l1 l2) w) = true ->
has_element l1 (find l1 w) = true \/
has_element l2 (find l2 w) = true.
intros [[l1 Hwf1] Ho1] [[l2 Hwf2] Ho2] w; unfold hunion;
unfold hunionl; unfold inter; unfold length; simpl.
apply (union1_contains_inv _ _ _ _ Hwf1 Hwf2).
Qed.

(*** DIFF ***)

Lemma WFo_diff :
forall l1 l2 : list,
well_formed_ordered l1 -> well_formed_ordered (diff l1 l2).
intros [l1 Hwf1] [l2 Hwf2]; unfold inter; simpl.
generalize l1 Hwf1; clear; induction l2; simpl.
auto.
intro l1; case (beq_nat (find l1 (witness (snd a))) 0); simpl.
apply IHl2.
intros Hwf1 Ho1; apply (IHl2 _ (WF_delete1 _ _ Hwf1)).
apply (WFo_delete1 l1 _ Ho1).
Qed.

Definition odiff (l1 l2 : oset) : oset :=
Build_oset (diff l1 l2) (WFo_diff l1 l2 (owf l1)).

(*** REPLACE_ELT ***)

Lemma WFo_replace_elt1 :
forall l : Rlist, well_formed l ->
forall e : element_t, forall cu : cursor,
(find l (witness e) = 0 \/ find l (witness e) = cu) ->
well_formed_ordered l ->
well_formed_ordered (replace_elt1
(fun l e => ceiling (delete1 l cu) (witness e)) l cu e).
intros l H e cu; unfold replace_elt1; simpl.
case_eq (has_element l cu); [|intros _ _ Hex; exact Hex].
intros Hhe Hfind Ho; assert (find (delete1 l cu) (witness e) = 0).
destruct Hfind as [Hfind|Hfind].
case_eq (O.eq_real_bool (witness e) (witness(element1 l cu))).
intro Heq; apply beq_real_true in Heq;
rewrite Heq; apply (delete1_find_deleted l cu Hhe H (ordered_hashed _ Ho)).
intro Hdiff; apply beq_real_false in Hdiff;
rewrite (delete1_find l _ cu Hhe Hdiff); exact Hfind.
rewrite <- Hfind in Hhe;
rewrite <- (find_element1 l (witness e) 1 (gt_Sn_O O) H
(position1_has_element _ _ _ Hhe)).
rewrite Hfind; rewrite Hfind in Hhe;
apply (delete1_find_deleted l cu Hhe H (ordered_hashed _ Ho)).
generalize (WFo_insert1 (delete1 l cu) e cu (WF_delete1 l cu H)).
unfold oinsert1; rewrite H0; rewrite <- beq_nat_refl.
intro HH; apply HH; apply WFo_delete1; exact Ho.
Qed.

Definition oreplace_eltl (l : list) (cu : cursor)
(e : element_t) : list :=
if (orb (beq_nat (find l (witness e)) 0)
(beq_nat (find l (witness e)) cu))
then Build_list (replace_elt1
(fun l e => ceiling (delete1 l cu) (witness e)) l cu e)
(WF_replace_elt1
(fun l e => ceiling (delete1 l cu) (witness e)) l cu e (wf l))
else l.

Lemma WFo_replace_elt : forall l : list, forall cu : cursor,
forall e : element_t,
well_formed_ordered l ->
well_formed_ordered (oreplace_eltl l cu e).
intros [l H] cu e; unfold oreplace_eltl; simpl.
case_eq ((beq_nat (find l (witness e)) 0 ||
beq_nat (find l (witness e)) cu)%bool); simpl.
intros Hfind; unfold replace_elt1; apply Bool.orb_true_elim in Hfind.
destruct Hfind as [Hfind|Hfind]; apply beq_nat_true in Hfind;
apply (WFo_replace_elt1 l H); [left|right]; exact Hfind.
intros _ Hex; exact Hex.
Qed.

Lemma oreplace_eltl_length :
forall l : list, forall cu : cursor, forall e : element_t,
length l = length (oreplace_eltl l cu e).
intros [l Hwf] cu e; unfold oreplace_eltl; unfold length; simpl.
case ((beq_nat (find l (witness e)) 0 ||
beq_nat (find l (witness e)) cu)%bool); [simpl|reflexivity].
apply (replace_elt1_length _ l cu e).
Qed.

Lemma oreplace_eltl_has_element :
forall l : list, forall cu cun : cursor, forall e : element_t,
has_element l cun = has_element (oreplace_eltl l cu e) cun.
intros [l Hwf] cu cun e; unfold oreplace_eltl; simpl.
case ((beq_nat (find l (witness e)) 0 ||
beq_nat (find l (witness e)) cu)%bool); [simpl|reflexivity].
apply (replace_elt1_has_element _ l cu cun e Hwf).
Qed.

Lemma oreplace_eltl_element :
forall l : list, forall cu cun : cursor, forall e : element_t,
cu <> cun -> has_element l cun = true ->
element l cun = element (oreplace_eltl l cu e) cun.
intros [l Hwf] cu cun e; unfold oreplace_eltl; unfold element; simpl.
case ((beq_nat (find l (witness e)) 0 ||
beq_nat (find l (witness e)) cu)%bool); [simpl|reflexivity].
apply (replace_elt1_element1 _ l cu cun e Hwf).
Qed.

Lemma oreplace_eltl_element_replaced :
forall l : list, forall cu : cursor, forall e : element_t,
find l (witness e) = 0 \/ find l (witness e) = cu ->
has_element l cu = true ->
element1 (oreplace_eltl l cu e) cu = e.
intros [l Hwf] cu e; unfold oreplace_eltl; unfold element; simpl.
case_eq ((beq_nat (find l (witness e)) 0 ||
beq_nat (find l (witness e)) cu)%bool); [intros _ _; simpl|intro Hko].
apply (replace_elt1_element1_replaced _ l cu e Hwf).
apply Bool.orb_false_elim in Hko; destruct Hko as [Hko1 Hko2];
intros [Hfind|Hfind]; [contradict Hko1|contradict Hko2];
rewrite Hfind; rewrite <- beq_nat_refl; apply Bool.diff_true_false.
Qed.

Lemma oreplace_eltl_find :
forall l : list, forall cu : cursor, forall e : element_t,
forall w : R, well_formed_ordered l ->
 witness e <> w -> find l w <> cu ->
find l w = find (oreplace_eltl l cu e) w.
intros [l Hwf] cu e w Ho; unfold oreplace_eltl; simpl.
case ((beq_nat (find l (witness e)) 0 ||
beq_nat (find l (witness e)) cu)%bool); [simpl|reflexivity].
apply (replace_elt1_find _ l _ _ _ Hwf (ordered_hashed l Ho)).
Qed.

Lemma oreplace_eltl_find_replaced :
forall l : list, forall cu : cursor, forall e : element_t,
well_formed_ordered l -> has_element l cu = true ->
find l (witness e) = 0 \/ find l (witness e) = cu ->
find (oreplace_eltl l cu e) (witness e) = cu.
intros [l Hwf] cu e Ho; unfold oreplace_eltl; simpl.
case_eq ((beq_nat (find l (witness e)) 0 ||
beq_nat (find l (witness e)) cu)%bool); [intros _; simpl|intro Hko].
apply (replace_elt1_find_replaced _ l _ _ Hwf (ordered_hashed l Ho)).
apply Bool.orb_false_elim in Hko; destruct Hko as [Hko1 Hko2];
intros _ [Hfind|Hfind]; [contradict Hko1|contradict Hko2];
rewrite Hfind; rewrite <- beq_nat_refl; apply Bool.diff_true_false.
Qed.

Definition oreplace_elt (m : oset) (cu : cursor) (e : element_t) : oset :=
Build_oset (oreplace_eltl m cu e) (WFo_replace_elt m cu e (owf m)).

(*** SUM_OF ***)

Module Type WeightType.

Parameter Inline weight : element_t -> nat.

End WeightType.

Module Sum_Of (W : WeightType).

Module Sum_List := Raw_List.Sum_Of(W).
Import Sum_List.

Lemma sum_of_equivalent :
forall l1 l2 : hset,
length l1 = length l2 -> 
(forall w : R,
      position l1 (find l1 w) > 0 ->
      (position l2 (find l2 w) > 0 /\
       W.weight(element l1 (find l1 w)) =
       W.weight(element l2 (find l2 w)))) ->
sum_of_weight l1 = sum_of_weight l2.
unfold position; unfold element;
unfold first; unfold length;
intros [[l1 Hwf1]Hh1] [[l2 Hwf2]Hh2]; simpl.
simpl in Hh1; simpl in Hh2.
case_eq l1; case_eq l2.
reflexivity.
simpl; intros a ll _ _ Hko; contradict Hko; apply O_S.
simpl; intros _ a ll _ Hko; symmetry in Hko;
contradict Hko; apply O_S.
intros a2 ll2 Hal2 a1 ll1 Hal1.
rewrite <- Hal1; rewrite <- Hal2; generalize Hwf1 Hh1 l2 Hwf2 Hh2;
clear; induction l1; simpl.
intros _ _ l2; case l2; simpl.
reflexivity.
intros aa ll _ _ Hko; contradict Hko; apply O_S.
intros [Hfst1[Hhe1 Hwf1]] [Hfind1 Hh1] l2 Hwf2 Hh2 Hlength Hw.
generalize (Hw (witness(snd a))).
rewrite beq_real_refl; rewrite <- beq_nat_refl.
intros Hint; destruct (Hint (gt_Sn_O O)) as [Hpo Hel]; clear Hint.
rewrite (sum_of_delete1 l2 _ (has_element_position1 _ _ _ Hpo)).
rewrite <- Hel;
rewrite (delete1_length l2 (find l2 (witness (snd a))) _
Hpo) in Hlength; apply eq_add_S in Hlength.
generalize Hwf2 Hh2; intros Hwfl2 Hhl2;
apply (WFh_delete1 l2 (find l2 (witness (snd a))) Hwf2) in Hh2;
apply (WF_delete1 l2 (find l2 (witness (snd a)))) in Hwf2.
rewrite (IHl1 Hwf1 Hh1 _ Hwf2 Hh2 Hlength); [reflexivity|clear IHl1].
intros w Hpl1w; generalize (Hw w).
case_eq (O.eq_real_bool (witness (snd a)) w);
[intro Heq; apply beq_real_true in Heq; contradict Hpl1w;
rewrite <- Heq; rewrite Hfind1;
rewrite (position1_no_element l1 Hwf1 1 (gt_Sn_O O)); apply gt_irrefl|].
case_eq (beq_nat (fst a) (find l1 w));
[intro Heq; apply beq_nat_true in Heq;
apply (has_element_position1) in Hpl1w; contradict Hpl1w;
rewrite <- Heq; rewrite Hhe1; apply Bool.diff_false_true|].
clear Hw; intros Heqafw Heqwaw Hint;
destruct (Hint (le_gt_trans _ _ _ (position1_has_element _ _ _
(has_element_position1 _ _ _ Hpl1w)) (gt_Sn_O 1))) as [Hw He];
clear Hint; apply beq_real_false in Heqwaw; split.
destruct (find_has_element (delete1 l2 (find l2 (witness (snd a)))) w).
apply (position1_has_element _ _ _ H).
rewrite (delete1_find _ _ _
(has_element_position1 _ _ _ Hpo)) in H.
contradict Hw; rewrite H;
rewrite (position1_no_element _ Hwfl2 _ (gt_Sn_O O)); apply gt_irrefl.
rewrite (find_element1 _ _ _ (gt_Sn_O O) Hwfl2 Hpo).
intro HH; apply Heqwaw; symmetry; exact HH.
rewrite He; rewrite (delete1_find _ _ _
(has_element_position1 _ _ _ Hpo)).
rewrite (delete1_element1 _ _ _ _ Hpo); [reflexivity|].
intro Heqfind; contradict Heqwaw.
rewrite <- (find_element1 l2 w 1 (gt_Sn_O O) Hwfl2 Hw).
rewrite <- (find_element1 l2 _ 1 (gt_Sn_O O) Hwfl2 Hpo).
rewrite Heqfind; reflexivity.
rewrite (find_element1 _ _ _ (gt_Sn_O O) Hwfl2 Hpo).
intro HH; apply Heqwaw; symmetry; exact HH.
Qed.

Lemma sum_of_insert_o :
forall l li : oset,
forall cu : cursor, forall e : element_t,
has_element li cu = true -> has_element l cu = false ->
element li cu = e ->
(forall cun : cursor,
has_element l cun = true ->
(witness (element l cun)) <> (witness e) /\
element li cun = element l cun /\
(Rgt (witness (element l cun)) (witness e) ->
position li cun = S(position l cun)) /\
(Rgt (witness e) (witness (element l cun)) ->
position l cun = position li cun)) ->
length li = S(length l) ->
sum_of_weight li =
(W.weight e) + sum_of_weight l.
intros [[l Hwf]Hh] [[li Hwfi]Hhi]; unfold position;
unfold element; unfold length; simpl.
intros cu e Hhelicu Hhelcu Hellicu Hcun Hlgth;
destruct (gt_O_eq cu) as [Hcu | Hko];
[|rewrite <- Hko in Hhelicu;
apply (position1_has_element _ _ 1) in Hhelicu;
contradict Hhelicu; rewrite (position1_no_element li Hwfi);
[apply le_Sn_n|apply gt_Sn_O]].
rewrite <- (Sum_List.sum_of_equivalent (insert1 l O cu e) li
(WF_insert1 l O e cu Hcu Hhelcu Hwf) Hwfi).
apply (sum_of_insert1 l O cu e Hhelcu).
apply (equivalent_insert1 l li Hwf Hwfi O cu e Hhelicu Hellicu Hhelcu);
[intros cun Hhelcun|apply Hlgth].
destruct (Hcun cun Hhelcun) as [Hwdiff[Hel[Hinf Hsup]]].
split; [| exact Hel].
destruct (Rtotal_order (witness e)
(witness (element1 l cun))) as [Hpinf | [Hpeq | Hpsup]].
apply (has_element_position1 _ _ 1); apply Rlt_gt in Hpinf.
rewrite (Hinf Hpinf); apply gt_Sn_O.
contradict Hwdiff; symmetry; exact Hpeq.
apply (has_element_position1 _ _ 1); rewrite <- (Hsup Hpsup);
apply (position1_has_element _ _ _ Hhelcun).
Qed.

Lemma sum_of_insert_h :
forall l li : hset,
forall cu : cursor, forall e : element_t,
has_element li cu = true -> has_element l cu = false ->
element li cu = e ->
(forall cun : cursor,
has_element l cun = true ->
has_element li cun = true /\
element li cun = element l cun) ->
length li = S(length l) ->
sum_of_weight li =
(W.weight e) + sum_of_weight l.
intros [[l Hwf]Hh] [[li Hwfi]Hhi]; unfold position;
unfold element; unfold length; simpl.
intros cu e Hhelicu Hhelcu Hellicu Hcun Hlgth;
destruct (gt_O_eq cu) as [Hcu | Hko];
[|rewrite <- Hko in Hhelicu;
apply (position1_has_element _ _ 1) in Hhelicu;
contradict Hhelicu; rewrite (position1_no_element li Hwfi);
[apply le_Sn_n|apply gt_Sn_O]].
rewrite <- (Sum_List.sum_of_equivalent (insert1 l O cu e) li
(WF_insert1 l O e cu Hcu Hhelcu Hwf) Hwfi).
apply (sum_of_insert1 l O cu e Hhelcu).
apply (equivalent_insert1 l li Hwf Hwfi O cu e Hhelicu Hellicu Hhelcu);
[intros cun Hhelcun|apply Hlgth].
destruct (Hcun cun Hhelcun) as [Hhe Hel].
split; [exact Hhe| exact Hel].
Qed.

End Sum_Of.



End Raw_Set.


