Require Import List.
Require Import Arith.
Require Import ZArith.
Require "list_raw".

Module Type ElementType.

Parameter Inline element_t : Set.

Parameter Inline e_nl : element_t.

Parameter Inline beq_elt : element_t -> element_t -> bool.

Axiom beq_elt_refl : forall e : element_t, beq_elt e e = true.

Axiom beq_elt_true : forall e1 : element_t, forall e2 : element_t,
beq_elt e1 e2 = true -> e1 = e2.

Axiom beq_elt_false : forall e1 : element_t, forall e2 : element_t,
beq_elt e1 e2 = false -> e1 <> e2.

End ElementType.

Module Raw_Vector (X: ElementType).

Module E.

Definition element_t : Set := X.element_t.

Definition witness_t : Set := X.element_t.

Definition witness (e : element_t) : witness_t := e.

Definition e_nl : element_t := X.e_nl.

Definition eq_witness (w1 w2 : witness_t) : Prop := w1 = w2.

Definition beq_witness (w1 w2 : witness_t) : bool := X.beq_elt w1 w2.

Lemma beq_witness_refl :
forall e : witness_t, beq_witness e e = true.
apply X.beq_elt_refl.
Qed.

Lemma beq_witness_true : forall e1 : witness_t, forall e2 : witness_t,
beq_witness e1 e2 = true -> eq_witness e1 e2.
apply X.beq_elt_true.
Qed.

Lemma beq_witness_false : forall e1 : witness_t, forall e2 : witness_t,
beq_witness e1 e2 = false -> not (eq_witness e1 e2).
apply X.beq_elt_false.
Qed.

End E.
Module ListR := list_raw.Raw_List(E).
Import ListR.

(*** TO_CURSOR ***)

Definition to_cursor (v : Rlist) (i : Z) :=
if (Zgt_bool i 0 && Zge_bool (Z_of_nat (List.length v)) i)%bool then
fst(nth(pred(Zabs_nat i)) v (0, X.e_nl)) else O.

Lemma bool_is_valid :
forall v : Rlist, forall i : Z,
if (Zgt_bool i 0 && Zge_bool (Z_of_nat (List.length v)) i)%bool then
Zge (Z_of_nat (List.length v)) i /\ Zgt i 0
else (Zle i 0 \/ Zgt i (Z_of_nat (List.length v))).
intros v i;
case_eq ((Zgt_bool i 0 && Zge_bool (Z_of_nat (List.length v)) i)%bool).
intro H; symmetry in H; apply Bool.andb_true_eq in H;
destruct H as [Hpos Hinf]; symmetry in Hinf; symmetry in Hpos.
generalize (Zgt_cases i 0); rewrite Hpos; clear Hpos; intro Hpos;
generalize (Zge_cases (Z_of_nat (List.length v)) i); rewrite Hinf;
clear Hinf; intro Hinf.
split; [exact Hinf|exact Hpos].
intro H; apply Bool.andb_false_elim in H; destruct H as [Hneg|Hsup];
[left|destruct (Z_le_gt_dec i 0) as [Hneg|Hpos];
[left; exact Hneg|right]].
generalize (Zgt_cases i 0); rewrite Hneg; clear Hneg; auto.
generalize (Zge_cases (Z_of_nat (List.length v)) i); rewrite Hsup;
clear Hsup; intro Hsup; apply Zlt_gt; exact Hsup.
Qed.

Lemma is_valid_bool_true :
forall v : Rlist, forall i : Z,
Zge (Z_of_nat (List.length v)) i /\ Zgt i 0 ->
(Zgt_bool i 0 && Zge_bool (Z_of_nat (List.length v)) i)%bool = true.
intros v i [Hinf Hpos]; apply andb_true_intro; split.
destruct (Zgt_is_gt_bool i 0) as [H _]; apply H; exact Hpos.
generalize (Zge_cases (Z_of_nat (List.length v)) i);
case (Zge_bool (Z_of_nat (List.length v)) i); [reflexivity|].
intro Hsup; contradict Hsup; apply Znot_lt_ge; exact Hinf.
Qed.

Lemma is_valid_bool_false :
forall v : Rlist, forall i : Z,
Zle i 0 \/ Zgt i (Z_of_nat (List.length v))  ->
(Zgt_bool i 0 && Zge_bool (Z_of_nat (List.length v)) i)%bool = false.
intros v i [Hin| Hpos]; [apply Bool.andb_false_intro1|
apply Bool.andb_false_intro2].
generalize (Zgt_cases i 0); case (Zgt_bool i 0); [|reflexivity].
intro Hko; contradict Hko; apply Zle_not_gt; exact Hin.
generalize (Zge_cases (Z_of_nat (List.length v)) i);
case (Zge_bool (Z_of_nat (List.length v)) i); [|reflexivity].
intro Hko; apply Zge_le in Hko; contradict Hko; apply Zgt_not_le;
exact Hpos.
Qed.

(*** TO_INDEX ***)

Fixpoint to_index1 (v : Rlist) (cu : cursor) (n : nat) :=
match v with
nil => 0
| a :: vs => if beq_nat cu (fst a) then n else to_index1 vs cu (S n)
end.

Definition to_index (v : Rlist) (cu : cursor) :=
Z_of_nat(to_index1 v cu 1).

Lemma to_index_int :
forall v : Rlist, forall cu : cursor,
Zge (Z_of_nat (List.length v)) (to_index v cu) /\ Zge (to_index v cu) 0.
unfold to_index; intros v cu; split; apply Zle_ge; [|apply Zle_0_nat].
apply inj_le; apply gt_S_le; rewrite (plus_n_O (List.length v));
rewrite plus_n_Sm; generalize 1 (gt_Sn_O O); induction v; simpl.
auto.
intros n _; case (beq_nat cu (fst a)).
apply le_gt_S; rewrite plus_comm; apply le_plus_trans; apply le_refl.
rewrite plus_n_Sm; apply IHv; apply gt_Sn_O.
Qed.

Lemma to_index1_sup :
forall v : Rlist, forall cu : cursor, forall n : nat,
to_index1 v cu n > 0 -> n <= to_index1 v cu n.
induction v; simpl.
intros _ n Hko; contradict Hko; apply gt_irrefl.
intros cu n; case (beq_nat cu (fst a)).
intros _; apply le_refl.
intro H; apply lt_le_weak; apply (IHv cu _ H).
Qed.

Lemma to_index_eq :
forall v : Rlist, forall cu1 cu2 : cursor,
to_index v cu1 = to_index v cu2 /\ Zgt (to_index v cu2) 0 ->
cu1 = cu2.
unfold to_index; intro v; generalize 1; induction v; simpl.
intros _ cu1 cu2 [_ Hko]; contradict Hko; apply Zgt_irrefl.
intros n cu1 cu2; case_eq (beq_nat cu1 (fst a));
case_eq (beq_nat cu2 (fst a)).
intros Hcu1 Hcu2 _; apply beq_nat_true in Hcu1; apply beq_nat_true in Hcu2;
rewrite Hcu1; rewrite Hcu2; reflexivity.
rewrite <- inj_0; intros _ _ [Heq Hpos]; apply inj_eq_rev in Heq;
apply inj_gt_rev in Hpos; generalize (to_index1_sup _ _ _ Hpos);
rewrite <- Heq; intro Hko; contradict Hko; apply le_Sn_n.
rewrite <- inj_0; intros _ _ [Heq Hpos]; apply inj_eq_rev in Heq;
apply inj_gt_rev in Hpos; rewrite <- Heq in Hpos;
generalize (to_index1_sup _ _ _ Hpos);
rewrite Heq; intro Hko; contradict Hko; apply le_Sn_n.
intros _ _; apply IHv.
Qed.

Lemma to_index_nl :
forall v : list,
(to_index v O = 0)%Z.
unfold to_index; intros [v Hwf]; generalize 1 Hwf; clear;
induction v; simpl.
reflexivity.
case (fst a).
intros n [Hko]; contradict Hko; apply gt_irrefl.
intros n m [_ [_ Hwf]]; apply (IHv _ Hwf).
Qed.

Lemma to_cursor_index1 :
forall v : Rlist, forall n m : nat,
well_formed v -> List.length v > n ->
to_index1 v (fst (nth n v (0, X.e_nl))) m = n + m.
induction v; simpl.
intros n m _ Hko; contradict Hko; apply le_not_gt; apply le_O_n.
intros n; case n; clear n.
rewrite <- beq_nat_refl; reflexivity.
intros n m;
case_eq (beq_nat (fst (nth n v (0, X.e_nl))) (fst a)).
intros Hko [Hfst [Hhe]]; apply beq_nat_true in Hko;
contradict Hko; generalize n Hfst Hhe; clear.
induction v; simpl.
intro n; case n; simpl; [|intros _]; intros Hko _ Heq; contradict Hko;
rewrite Heq; apply gt_irrefl.
intros n Hpos Hint; apply Bool.orb_false_elim in Hint.
destruct Hint as [Hdiff Hhe]; case n.
apply (beq_nat_false _ _ Hdiff).
clear n; intro n; apply (IHv n Hpos Hhe).
intros _ [_[_ Hwf]] Hl; apply gt_S_n in Hl.
rewrite (IHv n (S m) Hwf Hl).
rewrite <- plus_n_Sm; reflexivity.
Qed.

Lemma to_cursor_index :
forall v : list, forall i : Z,
to_index v (to_cursor v i) = i /\
Zge (Z_of_nat (length v)) i /\ Zgt i 0 \/
to_cursor v i = 0 /\
(Zle i 0 \/ Zgt i (Z_of_nat (length v))).
intros [v Hwf] i; unfold to_cursor; unfold to_index; simpl.
generalize (bool_is_valid v i);
case ((Zgt_bool i 0 && Zge_bool (Z_of_nat (List.length v)) i)%bool);
[intros [Hinf Hpos]; left|right].
split; [|split; [exact Hinf|exact Hpos]].
generalize Hpos Hinf;
rewrite <- Zabs_eq with i;[|apply Zlt_le_weak; apply Zgt_lt; apply Hpos].
rewrite <- inj_Zabs_nat; clear Hinf Hpos; rewrite <- inj_0;
intros Hpos Hinf; apply inj_eq; rewrite Zabs_nat_Z_of_nat;
apply inj_gt_rev in Hpos; apply Zge_le in Hinf; apply inj_le_rev in Hinf.
rewrite (S_pred _ _ Hpos) at 2; rewrite (S_pred _ _ Hpos) in Hinf;
apply le_S_gt in Hinf.
rewrite (plus_n_O (pred (Zabs_nat i))) at 2; rewrite plus_n_Sm.
apply (to_cursor_index1 v _ _ Hwf Hinf).
split; [reflexivity|exact H].
Qed.

(*** ELEMENT ***)

Definition element (v : Rlist) (i : Z) :=
let n :=
if (Zgt_bool i 0 && Zge_bool (Z_of_nat (List.length v)) i)%bool then
Zabs_nat i else O in
if beq_nat n O then X.e_nl else snd(nth (pred n) v (0, X.e_nl)).

(*** FIND ***)

Fixpoint find2 (v : Rlist) (e : X.element_t) (i : nat) : nat :=
match v with
nil => O
| a :: vs => if X.beq_elt (snd a) e then i else find2 vs e (S i)
end.

Fixpoint find1 (v : Rlist) (e : X.element_t) (n : nat) (i : nat) : nat :=
match v with
nil => O
| a :: vs => if beq_nat n i then find2 v e i else find1 vs e n (S i)
end.

Definition find (v : Rlist) (e : X.element_t) (i : Z) : nat :=
let n := 
if (Zgt_bool i 0 && Zge_bool (Z_of_nat (List.length v)) i)%bool then
Zabs_nat i else O in
if beq_nat n 0 then find2 v e 1 else find1 v e n 1.

Lemma find_case : 
forall v : Rlist, forall e : X.element_t, forall i : Z,
Zge (Z_of_nat (List.length v)) i /\ Zgt i 0 ->
Raw_Vector.find v e i = O \/
Raw_Vector.find v e i <= List.length v /\
Zabs_nat i <= Raw_Vector.find v e i.
unfold find;
intros v e i Hin; rewrite is_valid_bool_true; [|exact Hin].
destruct Hin as [_ Hpi]; apply Zgt_lt in Hpi;
generalize (Zabs_nat_lt _ _ (conj (Zle_refl 0) Hpi));
rewrite <- inj_0; rewrite Zabs_nat_Z_of_nat.
case_eq (beq_nat (Zabs_nat i) 0); [intros Heq Hko; contradict Hko;
apply beq_nat_true in Heq; rewrite Heq; apply gt_irrefl|intros _].
rewrite (pred_Sn (List.length v)); rewrite (plus_n_O (List.length v));
rewrite plus_n_Sm.
generalize (Zabs_nat i) 1; clear; intro i; induction v.
simpl; left; reflexivity.
intro n; unfold find1; fold find1.
case_eq (beq_nat i n).
intros Heq Hpos;
apply beq_nat_true in Heq; rewrite Heq.
generalize (a :: v) n; clear; induction l; simpl.
intros n; left; reflexivity.
case (X.beq_elt (snd a) e); intros n; [right|].
split; [apply le_plus_r|apply le_refl].
destruct (IHl (S n)) as [Hf|[Hi Hs]]; [left; exact Hf|right].
rewrite <- plus_n_Sm in Hi; rewrite <- pred_Sn in Hi.
split; [exact Hi|apply lt_le_weak; exact Hs].
simpl List.length; rewrite plus_Sn_m; rewrite plus_n_Sm.
intros _; apply IHv.
Qed.

Lemma find2_sup :
forall v : Rlist, forall e : X.element_t,
forall n : nat,
find2 v e n > O -> n <= find2 v e n.
intros v e; induction v; simpl.
intros n Hko; contradict Hko; apply gt_irrefl.
case (X.beq_elt (snd a) e).
intros; apply le_refl.
intros n Hfind; apply (le_trans _ _ _ (le_n_Sn n)); apply IHv;
exact Hfind.
Qed.

Lemma find1_sup :
forall v : Rlist, forall e : X.element_t,
forall i n : nat,
find1 v e i n > O -> n <= find1 v e i n.
intros v e; induction v.
simpl; intros i n Hko; contradict Hko; apply gt_irrefl.
unfold find1; fold find1; intros i n; case (beq_nat i n).
apply find2_sup.
intros Hfind; apply (le_trans _ _ _ (le_n_Sn n)); apply IHv;
exact Hfind.
Qed.

Lemma find2_element :
forall v : Rlist, forall e : X.element_t,
forall n : nat,
find2 v e n > O ->
snd(nth (find2 v e n - n) v (0, X.e_nl)) = e.
intros v e; induction v; simpl.
intros _ Hko; contradict Hko; apply gt_irrefl.
case_eq (X.beq_elt (snd a) e).
intros Hea n _; rewrite minus_diag; apply X.beq_elt_true; exact Hea.
intros Hea n; case_eq (find2 v e (S n) - n).
intros Hko Hp.
apply find2_sup in Hp.
apply (minus_le_compat_r _ _ n) in Hp. rewrite Hko in Hp;
rewrite <- minus_Sn_m in Hp; [|apply le_refl]; rewrite minus_diag in Hp;
contradict Hp; apply le_Sn_n.
intros m Hm Hfind.
rewrite (minus_plus_simpl_l_reverse _ _ 1) in Hm;
simpl plus in Hm; rewrite <- minus_Sn_m in Hm;
[apply eq_add_S in Hm; rewrite <- Hm; apply IHv|apply find2_sup];
exact Hfind.
Qed.

Lemma find1_element :
forall v : Rlist, forall e : X.element_t, forall i n : nat,
find1 v e i n > O ->
snd(nth (find1 v e i n - n) v (O,X.e_nl)) = e.
intros v e i; induction v.
simpl; intros n Hko; contradict Hko; apply gt_irrefl.
unfold find1; fold find1; intros n; case (beq_nat i n).
intros Hf; apply (find2_element _ e _ Hf).
intros Hp; simpl; case_eq (find1 v e i (S n) - n).
intros Hko; apply find1_sup in Hp.
apply (minus_le_compat_r _ _ n) in Hp. rewrite Hko in Hp;
rewrite <- minus_Sn_m in Hp; [|apply le_refl]; rewrite minus_diag in Hp;
contradict Hp; apply le_Sn_n.
intros m Hm; rewrite (minus_plus_simpl_l_reverse _ _ 1) in Hm;
simpl plus in Hm; rewrite <- minus_Sn_m in Hm;
[apply eq_add_S in Hm;
rewrite <- Hm; apply IHv|apply find1_sup]; exact Hp.
Qed.

Lemma find_element :
forall v : Rlist, forall e : X.element_t, forall i : Z,
Zge (Z_of_nat (List.length v)) i /\ Zgt i 0 ->
find v e i <= List.length v ->
Zabs_nat i <= find v e i ->
Raw_Vector.element v (Z_of_nat (Raw_Vector.find v e i)) = e.
unfold element;
intros v e i [Hli Hpi] Hlf Hpf.
rewrite (is_valid_bool_true v _); [| apply inj_le in Hlf;
apply inj_le in Hpf; apply Zle_ge in Hlf; rewrite inj_Zabs_nat in Hpf;
rewrite <- (Zabs_eq i (Zlt_le_weak _ _ (Zgt_lt _ _ Hpi) ))in Hpi;
split; [exact Hlf|apply (Zle_gt_trans _ _ _ Hpf Hpi)]].
repeat(rewrite Zabs_nat_Z_of_nat).
generalize Hlf Hpf Hli Hpi; unfold find; unfold to_cursor.
rewrite (is_valid_bool_true v _); [|split; [exact Hli|exact Hpi]].
rewrite <- (Zabs_eq i (Zlt_le_weak _ _ (Zgt_lt _ _ Hpi) )).
rewrite <- inj_Zabs_nat; rewrite <- inj_0;
repeat(rewrite Zabs_nat_Z_of_nat); clear.
case_eq (beq_nat (Zabs_nat i) 0); [intros Heq _ _ _ Hko; contradict Hko|].
apply beq_nat_true in Heq; rewrite Heq; apply Zgt_irrefl.
intros _ Hfl Hif Hil Hpi; apply Zge_le in Hil;
apply inj_le_rev in Hil; apply inj_gt_rev in Hpi.
case_eq (beq_nat (find1 v e (Zabs_nat i) 1) 0); [|intros _].
intro Hko; apply beq_nat_true in Hko; contradict Hif;
rewrite Hko; apply gt_not_le. exact Hpi.
rewrite pred_of_minus; simpl; rewrite find1_element.
reflexivity.
apply le_gt_trans with (Zabs_nat i); [exact Hif|exact Hpi].
Qed.

Lemma find2_is_first :
forall v : Rlist, forall e : X.element_t,
forall k : nat, forall n : nat,
n > O -> find2 v e n > k /\ n <= k ->
snd(nth (k - n) v (O,X.e_nl)) <> e.
intros v e; induction v; simpl.
intros k n Hn [Hinf Hsup]; apply (le_gt_trans _ _ _ Hsup) in Hn;
contradict Hinf; apply gt_asym; exact Hn.
intros k n; case_eq (k - n).
case_eq (X.beq_elt (snd a) e).
intros _ _ _ [Hsup Hinf]; contradict Hinf; apply gt_not_le; exact Hsup.
intros Hex _ _ _; apply X.beq_elt_false; exact Hex.
intros ko Hkko; rewrite (pred_Sn ko);
generalize (gt_Sn_O ko); rewrite <- Hkko; clear ko Hkko.
case (X.beq_elt (snd a) e).
intros _ _ [Hsup Hinf]; contradict Hinf; apply gt_not_le; exact Hsup.
assert (pred(k-n)=k-(S n)); [|rewrite H].
rewrite pred_of_minus.
generalize n; clear; induction k; simpl; [reflexivity|].
intro n; case n; simpl; [reflexivity|apply IHk].
intros Hk Hn [Hf Hnk].
apply le_lt_eq_dec in Hnk; destruct Hnk as [Hnk | Hko].
unfold lt in Hnk; apply (IHv k (S n) (gt_Sn_O n));
split; [exact Hf|exact Hnk].
contradict Hk; rewrite Hko; rewrite minus_diag; apply gt_irrefl.
Qed.

Lemma find1_is_first :
forall v : Rlist, forall e : X.element_t,
forall i k : nat, forall n : nat,
i > 0 -> k > 0 -> n <= i ->
find1 v e i n > k /\ i <= k ->
snd(nth (k - n) v (O,X.e_nl)) <> e.
intros v e i; induction v.
simpl; intros k n _ Hko _ [Hgt]; contradict Hko; apply gt_asym; exact Hgt.
intros k n; unfold find1; fold find1; case_eq (beq_nat i n).
intros Heq Hi _ _; apply beq_nat_true in Heq; rewrite Heq in Hi;
rewrite Heq; apply (find2_is_first _ e k n Hi).
simpl; intros Hdiff Hi Hk Hni; apply le_lt_eq_dec in Hni;
destruct Hni as [Hni | Hko]; [|contradict Hdiff; rewrite Hko;
rewrite <- beq_nat_refl; apply Bool.diff_true_false].
intros [Hf Hik]; case_eq (k - n).
generalize (le_gt_trans _ _ _ Hik Hni); intro Hkn.
apply gt_le_S in Hkn; apply (minus_le_compat_r _ _ n) in Hkn;
rewrite <- minus_Sn_m in Hkn; [|apply le_refl]; rewrite minus_diag in Hkn;
intro Hko; contradict Hkn; rewrite Hko; apply le_Sn_n.
intros ko Hkko; rewrite (pred_Sn ko);
generalize (gt_Sn_O ko); rewrite <- Hkko; clear ko Hkko.
assert (pred(k-n)=k-(S n)); [|rewrite H].
rewrite pred_of_minus.
generalize n; clear; induction k; simpl; [reflexivity|].
intro n; case n; simpl; [reflexivity|apply IHk].
intros _; apply (IHv k (S n)Hi Hk (gt_le_S _ _ Hni));
split; [exact Hf|exact Hik].
Qed.

Lemma find_is_first :
forall v : Rlist, forall e : X.element_t,
forall i k : Z,
Zge (Z_of_nat (List.length v)) i /\ Zgt i 0 ->
Zgt (Z_of_nat (find v e i)) k /\ Zge k i ->
find v e i <= List.length v ->
element v k <> e.
intros v e i k [Hli Hpi] [Hfk Hki] Hfl;
generalize (Zle_gt_trans _ _ _ (Zge_le _ _ Hki) Hpi); intro Hpk;
generalize (Zle_trans _ _ _ (Zlt_le_weak _ _ (Zgt_lt _ _ Hfk))
(inj_le _ _ Hfl)); intro Hlk; apply Zle_ge in Hlk.
generalize Hfk; unfold find; unfold element; unfold to_cursor;
rewrite (is_valid_bool_true v i); [|split; [exact Hli|exact Hpi]];
rewrite (is_valid_bool_true v k); [|split; [exact Hlk|exact Hpk]].
generalize Hpi Hpk Hki;
apply Zgt_lt in Hpi; apply Zgt_lt in Hpk;
apply Zlt_le_weak in Hpi; apply Zlt_le_weak in Hpk;
rewrite <- (Zabs_eq i Hpi); rewrite <- (Zabs_eq k Hpk).
repeat (rewrite <- inj_Zabs_nat); rewrite <- inj_0; clear;
repeat(rewrite Zabs_nat_Z_of_nat).
case_eq (beq_nat (Zabs_nat i) 0); [intros Heq Hko; contradict Hko;
apply beq_nat_true in Heq; rewrite Heq; apply Zgt_irrefl|intros _].
intros Hpi Hpk Hki Hfk.
apply Zge_le in Hki; apply inj_le_rev in Hki;
apply inj_gt_rev in Hpi; apply inj_gt_rev in Hpk;
apply inj_gt_rev in Hfk.
case_eq (beq_nat (Zabs_nat k) 0); [intro Hko;
apply beq_nat_true in Hko; contradict Hpk; rewrite Hko;
apply gt_irrefl|intros _].
rewrite pred_of_minus; apply (find1_is_first v e _ _ _ Hpi Hpk).
apply gt_le_S; exact Hpi.
split; [exact Hfk|exact Hki].
Qed.

Lemma find2_is_first_O :
forall v : Rlist, forall e : X.element_t,
forall k : nat, forall n : nat,
k <= List.length v /\ k > O ->
n > O -> find2 v e n = O ->
snd(nth (pred k) v (O,X.e_nl)) <> e.
intros v e; induction v; simpl.
intros k n [Hinf Hsup]; contradict Hinf; apply gt_not_le;
exact Hsup.
intro k; case k.
intros n [_ Hko]; contradict Hko; apply gt_irrefl.
clear k; intros k n; simpl; case_eq k.
case_eq (X.beq_elt (snd a) e).
intros _ _ _ Hko Heq; contradict Hko; rewrite Heq; apply gt_irrefl.
intros Hex _ _ _ _; apply X.beq_elt_false; exact Hex.
intros ko Hkko; rewrite (pred_Sn ko) at 3;
generalize (gt_Sn_O ko); rewrite <- Hkko; clear ko Hkko.
case (X.beq_elt (snd a) e).
intros _ _ Hko Heq; contradict Hko; rewrite Heq; apply gt_irrefl.
intros Hk [Hl _] _; apply le_S_n in Hl; generalize (gt_Sn_O n);
apply (IHv k (S n)); split; [exact Hl|exact Hk].
Qed.

Lemma find1_is_first_O :
forall v : Rlist, forall e : X.element_t,
forall i k n : nat,
i > 0 ->
k <= List.length v /\ k > 0 ->
n <= i -> k + n > i -> find1 v e i n = O ->
snd(nth (pred k) v (O,X.e_nl)) <> e.
intros v e; induction v.
simpl; intros i k n _ [Hinf Hgt]; contradict Hinf;
apply gt_not_le; exact Hgt.
intros i k n;
unfold find1; fold find1; case_eq (beq_nat i n).
intro Heq; apply beq_nat_true in Heq; rewrite Heq;
intros Hn Hk _ _; apply (find2_is_first_O _ e k n Hk Hn).
case k; [intros _ _ [_ Hko]; contradict Hko; apply gt_irrefl|].
clear k; intros k Hdiff; simpl.
case_eq k; simpl.
intros _ _ _ Hle1 Hle2; apply gt_le_S in Hle2; apply le_S_n in Hle2;
contradict Hdiff; rewrite (le_antisym _ _ Hle1 Hle2);
rewrite <- beq_nat_refl; apply Bool.diff_true_false.
intros ko Hkko; rewrite (pred_Sn ko) at 4; rewrite <- plus_Sn_m;
generalize (gt_Sn_O ko); rewrite <- Hkko; clear ko Hkko.
intros Hpk Hpi [Hkl _] Hni; rewrite plus_n_Sm;
apply le_S_n in Hkl; apply le_lt_or_eq in Hni;
destruct Hni as [Hni|Hko]; [unfold lt in Hni|].
generalize Hni; apply (IHv i k (S n) Hpi);
split; [exact Hkl|exact Hpk].
contradict Hdiff; rewrite Hko; rewrite <- beq_nat_refl;
apply Bool.diff_true_false.
Qed.

Lemma find_is_first_O :
forall v : Rlist, forall e : X.element_t,
forall i k : Z,
Zge (Z_of_nat (List.length v)) i /\ Zgt i 0 ->
Zge (Z_of_nat (List.length v)) k /\ Zge k i ->
find v e i = O ->
element v k <> e.
intros v e i k [Hli Hpi] [Hlk Hki];
generalize (Zle_gt_trans _ _ _ (Zge_le _ _ Hki) Hpi); intro Hpk.
unfold find; unfold element; unfold to_cursor;
rewrite (is_valid_bool_true v i); [|split; [exact Hli|exact Hpi]];
rewrite (is_valid_bool_true v k); [|split; [exact Hlk|exact Hpk]].
generalize Hli Hpi Hlk Hki Hpk;
apply Zgt_lt in Hpi; apply Zgt_lt in Hpk;
apply Zlt_le_weak in Hpi; apply Zlt_le_weak in Hpk;
rewrite <- (Zabs_eq i Hpi); rewrite <- (Zabs_eq k Hpk).
repeat (rewrite <- inj_Zabs_nat); rewrite <- inj_0; clear;
intros Hli Hpi Hlk Hki Hpk; repeat(rewrite Zabs_nat_Z_of_nat).
apply Zge_le in Hli; apply inj_le_rev in Hli;
apply Zge_le in Hlk; apply inj_le_rev in Hlk;
apply inj_gt_rev in Hpi; apply inj_gt_rev in Hpk;
apply Zge_le in Hki; apply inj_le_rev in Hki.
case_eq (beq_nat (Zabs_nat k) 0); [intro Hko;
apply beq_nat_true in Hko; contradict Hpk; rewrite Hko;
apply gt_irrefl|intros _].
case_eq (beq_nat (Zabs_nat i) 0); [intro Heq; contradict Hpi;
apply beq_nat_true in Heq; rewrite Heq; apply gt_irrefl|intros _].
apply le_gt_S in Hki; generalize Hki;
rewrite (plus_n_O (Zabs_nat k)) at 1; rewrite plus_n_Sm;
generalize Hpi; intro HH; apply gt_le_S in HH;
generalize HH; apply (find1_is_first_O v e _ _ _ Hpi).
split; [exact Hlk|exact Hpk].
Qed.

(*** LEFT ***)

Definition left1 (v : Rlist) (i : Z) :=
let n :=
if (Zgt_bool i 0 && Zge_bool (Z_of_nat (List.length v)) i)%bool then
Zabs_nat i else O in
if beq_nat n O then v else firstn (pred n) v.

Lemma left1_length :
forall v : Rlist, forall i : Z,
Zge (Z_of_nat (List.length v + 1)) i /\ Zgt i 0 ->
Z_of_nat (List.length (left1 v i) + 1) = i.
intros v i; unfold left1.
generalize (bool_is_valid v i);
case ((Zgt_bool i 0 && Zge_bool (Z_of_nat (List.length v)) i)%bool).
intros [Hli Hpi] _; generalize Hli Hpi;
rewrite <- (Zabs_eq i (Zlt_le_weak _ _ (Zgt_lt _ _ Hpi)));
rewrite <- inj_Zabs_nat; rewrite <- inj_0;
rewrite Zabs_nat_Z_of_nat.
clear; intros Hli Hpi; apply Zge_le in Hli;
apply inj_le_rev in Hli; apply inj_gt_rev in Hpi.
case_eq (beq_nat (Zabs_nat i) 0).
intro Hko; contradict Hpi; apply beq_nat_true in Hko;
rewrite Hko; apply gt_irrefl.
intros _; apply inj_eq; rewrite firstn_length.
rewrite (Min.min_l _ _ (le_trans _ _ _ (le_pred_n _) Hli)).
rewrite <- plus_n_Sm; rewrite <- plus_n_O.
symmetry; apply S_pred with O; exact Hpi.
intros [Hko|Hgt] [Hge Hp]; rewrite <- beq_nat_refl;
[contradict Hko; apply Zgt_not_le; exact Hp|].
generalize Hge Hgt; clear Hge Hgt;
rewrite <- (Zabs_eq i (Zlt_le_weak _ _ (Zgt_lt _ _ Hp)));
rewrite <- plus_n_Sm; rewrite <- plus_n_O;
rewrite <- inj_Zabs_nat; intros Hge Hgt.
apply Zge_le in Hge; apply inj_le_rev in Hge;
apply inj_gt_rev in Hgt; apply inj_eq.
apply le_lt_eq_dec in Hge; destruct Hge as [Hko|Hex].
contradict Hko; unfold lt; apply gt_not_le; apply gt_n_S; exact Hgt.
symmetry; exact Hex.
Qed.

Lemma left1_element :
forall v : Rlist, forall i j : Z,
Zge (Z_of_nat (List.length v + 1)) i /\ Zgt i 0 ->
Zlt 0 j /\ Zlt j i ->
element (left1 v i) j = element v j.
unfold element; intros v i j Hi.
generalize (bool_is_valid v j);
case ((Zgt_bool j 0 && Zge_bool (Z_of_nat (List.length v)) j)%bool).
generalize (bool_is_valid (left1 v i) j);
case ((Zgt_bool j 0 && Zge_bool
(Z_of_nat (List.length (left1 v i))) j)%bool).
intros _ [_ Hjp]; rewrite <- inj_0;
rewrite <- (Zabs_eq j (Zlt_le_weak _ _ (Zgt_lt _ _ Hjp))).
rewrite <- inj_Zabs_nat; rewrite Zabs_nat_Z_of_nat;
clear Hjp; intros [Hjp Hij]; apply Zlt_gt in Hjp;
apply inj_gt_rev in Hjp; apply Zlt_gt in Hij.
case_eq (beq_nat (Zabs_nat j) 0);
[intro Hko; contradict Hjp; apply beq_nat_true in Hko;
rewrite Hko; apply gt_irrefl|intro Hdiff; unfold left1].
unfold to_cursor; generalize (bool_is_valid v i);
case ((Zgt_bool i 0 && Zge_bool (Z_of_nat (List.length v)) i)%bool).
intros [Hli Hip]; generalize Hli Hip Hij;
rewrite <- (Zabs_eq i (Zlt_le_weak _ _ (Zgt_lt _ _ Hip)));
rewrite <- inj_0 ; rewrite <- inj_Zabs_nat;
clear Hli Hip Hij; intros Hli Hip Hij; apply inj_gt_rev in Hip;
apply Zge_le in Hli; apply inj_le_rev in Hli.
rewrite Zabs_nat_Z_of_nat; apply inj_gt_rev in Hij. 
case_eq (beq_nat (Zabs_nat i) 0);
[intro Hko; contradict Hip; apply beq_nat_true in Hko;
rewrite Hko; apply gt_irrefl| intros _].
generalize (Zabs_nat i) v (Zabs_nat j) Hjp Hli Hij; clear.
induction n; simpl.
intros v j Hs _ Hi; contradict Hs; apply gt_asym; exact Hi.
case_eq n; simpl.
intros _ v m Hs _ Hi; contradict Hs; apply le_not_gt;
apply gt_S_le; exact Hi.
intros i Hni v j; case v; simpl; [reflexivity|].
case_eq (pred j); simpl; [reflexivity|].
rewrite (pred_Sn i); rewrite <- Hni.
intros n0 Hn0j _ l Hjp; rewrite (pred_Sn n0); rewrite (S_pred j _ Hjp);
rewrite <- Hn0j; intros Hnl Hnj; apply le_S_n in Hnl; apply gt_S_n in Hnj.
generalize Hnl Hnj; rewrite <- (S_pred n 0); [apply IHn|];
[rewrite Hn0j; apply gt_Sn_O|rewrite Hni; apply lt_O_Sn].
rewrite <- beq_nat_refl; reflexivity.
intros [Hko | Hko] _ [Hjp Hji].
apply Zlt_gt in Hjp; contradict Hjp; apply Zle_not_gt; exact Hko.
apply Zgt_le_succ in Hko; rewrite <- inj_S in Hko;
rewrite (plus_n_O (List.length (left1 v i))) in Hko;
rewrite plus_n_Sm in Hko.
rewrite (left1_length v i Hi) in Hko; contradict Hko; apply Zgt_not_le;
apply Zlt_gt; exact Hji.
intros [Hko|Hko] [Hjp Hji].
apply Zlt_gt in Hjp; contradict Hjp; apply Zle_not_gt; exact Hko.
apply Zgt_le_succ in Hko; rewrite <- inj_S in Hko;
rewrite (plus_n_O (List.length v)) in Hko; rewrite plus_n_Sm in Hko.
destruct Hi as [Hil _]; apply Zge_le in Hil; contradict Hil;
apply Zgt_not_le; apply (Zgt_le_trans _ _ _ (Zlt_gt _ _ Hji) Hko).
Qed.

Lemma left1_to_index1 :
forall v : Rlist, forall cu : cursor, forall n i : nat,
List.length v > i -> to_index1 v cu n > 0 ->
i + n > to_index1 v cu n ->
to_index1 (firstn i v) cu n = to_index1 v cu n.
induction v; simpl.
intros cu n i _ Hko; contradict Hko; apply le_not_gt; apply le_O_n.
intros cu n i; case i; clear i; simpl.
case (beq_nat cu (fst a)); intros _ Hp Hko; contradict Hko;
apply le_not_gt;
[apply le_refl|apply lt_le_weak; apply to_index1_sup; exact Hp].
intros i; case (beq_nat cu (fst a)).
reflexivity.
intros Hl Hp Hi; rewrite plus_n_Sm in Hi; apply gt_S_n in Hl;
apply (IHv cu (S n) i Hl Hp Hi).
Qed.

Lemma left1_to_index1_inv :
forall v : Rlist, forall cu : cursor, forall n i : nat,
List.length v > i -> to_index1 (firstn i v) cu n > 0 ->
to_index1 (firstn i v) cu n = to_index1 v cu n.
induction v; simpl.
intros cu n i Hko; contradict Hko; apply le_not_gt; apply le_O_n.
intros cu n i; case i; clear i; simpl.
intros _ Hko; contradict Hko; apply gt_irrefl.
intros i; case (beq_nat cu (fst a)).
reflexivity.
intros Hl Hp; apply gt_S_n in Hl;
apply (IHv cu (S n) i Hl Hp).
Qed.

Lemma left1_to_index :
forall v : Rlist, forall i : Z, forall cu : cursor,
Zge (Z_of_nat (List.length v + 1)) i /\ Zgt i 0 ->
(Zlt 0 (to_index v cu) /\ Zlt (to_index v cu) i \/
Zlt 0 (to_index (left1 v i) cu)) ->
to_index (left1 v i) cu = to_index v cu.
unfold has_element; unfold left1; intros v i cu [_ Hip].
generalize (bool_is_valid v i);
case ((Zgt_bool i 0 && Zge_bool (Z_of_nat (List.length v)) i)%bool);
[|rewrite <- beq_nat_refl; reflexivity].
rewrite <- inj_0; rewrite <- (Zabs_eq i (Zlt_le_weak _ _ (Zgt_lt _ _ Hip))).
rewrite <- inj_Zabs_nat; rewrite Zabs_nat_Z_of_nat;
clear Hip; intros [Hil Hip]; apply Zge_le in Hil;
apply inj_le_rev in Hil; apply inj_gt_rev in Hip.
rewrite (S_pred _ _ Hip) in Hil; apply le_S_gt in Hil;
case(beq_nat (Zabs_nat i) 0); [reflexivity|unfold to_index].
intros [[Hp Hi]|Hp]; apply Zlt_gt in Hp;
apply inj_gt_rev in Hp; apply inj_eq.
apply Zlt_gt in Hi; apply inj_gt_rev in Hi.
rewrite (S_pred _ _ Hip) in Hi; 
rewrite (plus_n_O (pred (Zabs_nat i))) in Hi; rewrite plus_n_Sm in Hi.
apply (left1_to_index1 v cu 1 _ Hil Hp Hi).
apply (left1_to_index1_inv v cu 1 _ Hil Hp).
Qed.

Lemma Wf_left1 :
forall v : list, forall i : Z, well_formed (left1 v i).
intros [v Hwf]; simpl; unfold left1.
intro i;
case ((Zgt_bool i 0 && Zge_bool (Z_of_nat (List.length v)) i)%bool);
[|rewrite <- beq_nat_refl; exact Hwf].
case (beq_nat (Zabs_nat i) 0); [exact Hwf|].
generalize (pred (Zabs_nat i)) Hwf; clear; induction v; simpl.
intro n; case n; simpl; auto.
intro n; case n; clear n; simpl; [auto|intro n].
intros [Hfst[Hhe Hwf]]; split; [|split];
[exact Hfst|generalize n Hhe; clear|apply (IHv n Hwf)].
induction v; simpl.
intro n; case n; simpl; auto.
intro n; case n; clear n; simpl; [auto|intro n].
intros Hint; apply Bool.orb_false_elim in Hint; destruct Hint as [Heq Hhe];
rewrite Heq; rewrite Bool.orb_false_l; apply (IHv n Hhe).
Qed.

Definition left (v : list) (i : Z) : list :=
Build_list (left1 v i) (Wf_left1 v i).

(*** INVALIDATE ***)

Module Type Invalidate.

Parameter invalidate : Rlist -> nat -> Rlist.

Axiom invalidate_element :
forall l : Rlist, forall m n : nat,
snd(nth n (invalidate l m) (0, X.e_nl)) = snd(nth n l (O, X.e_nl)).

Axiom invalidate_to_index :
forall l : Rlist,forall m n : nat, forall cu : cursor,
(to_index1 l cu n > 0 /\ m + n > (to_index1 l cu n) \/
to_index1 (invalidate l m) cu n > 0 /\
m + n > (to_index1 (invalidate l m) cu) n) ->
to_index1 (invalidate l m) cu n = to_index1 l cu n.

Axiom invalidate_length :
forall l : Rlist, forall m : nat,
List.length (invalidate l m) = List.length l.

Axiom wf_invalidate :
forall l : Rlist, forall m : nat, well_formed(l) ->
well_formed(invalidate l m).

End Invalidate.

Module Shift : Invalidate.

Fixpoint shift (l : Rlist) (last : cursor) (e : X.element_t) :=
match l with
nil => (last, e)::nil
| a :: ls => (fst a, e) :: (shift ls last (snd a))
end.

Fixpoint invalidate (l : Rlist) (n : nat) : Rlist :=
match l with
  nil => nil
| a :: ls => match n with
     O => shift ls (fst a) (snd a)
   | S m => a :: invalidate ls m
   end
end.

Lemma shift_element :
forall l : Rlist, forall cu : cursor,
forall e : X.element_t, forall n : nat,
snd (nth n (shift l cu e) (0, X.e_nl)) =
snd (nth n ((cu, e) :: l) (O, X.e_nl)).
intros l cu; induction l; simpl.
reflexivity.
intros e n; case n; clear n.
simpl; reflexivity.
intros n; rewrite IHl; simpl; case n; reflexivity.
Qed.

Lemma invalidate_element :
forall l : Rlist, forall m n : nat,
snd (nth n (invalidate l m) (0, X.e_nl)) = snd (nth n l (O, X.e_nl)).
induction l; simpl.
reflexivity.
intros m n; case m; clear m.
rewrite shift_element; simpl; case n; reflexivity.
intros m; simpl; case n; [reflexivity|].
clear n; intro n; apply IHl.
Qed.

Lemma invalidate_to_index :
forall l : Rlist, forall m n : nat, forall cu : cursor,
(to_index1 l cu n > 0 /\ m + n > (to_index1 l cu n) \/
to_index1 (invalidate l m) cu n > 0 /\
m + n > (to_index1 (invalidate l m) cu) n) ->
to_index1 (invalidate l m) cu n = to_index1 l cu n.
induction l; simpl.
intros m n _ [[Hko _]|[Hko _]]; contradict Hko; apply gt_irrefl.
intros m n cu; case m; clear m.
case (beq_nat cu (fst a)); simpl.
intros [[_ Hko]|[Hp Hko]]; contradict Hko; [apply gt_irrefl|].
apply le_not_gt; apply to_index1_sup; exact Hp.
intros [[Hp Hko]|[Hp Hko]]; contradict Hko;
apply le_not_gt; [apply lt_le_weak|]; apply to_index1_sup; exact Hp.
intro m; simpl; case (beq_nat cu (fst a)); simpl.
reflexivity.
rewrite plus_n_Sm; apply IHl.
Qed.

Lemma shift_length :
forall l : Rlist, forall cu : cursor, forall e : X.element_t,
List.length (shift l cu e) = S (List.length l).
induction l; simpl.
reflexivity.
intros cu _; rewrite IHl; reflexivity.
Qed.

Lemma invalidate_length :
forall l : Rlist, forall m : nat,
List.length (invalidate l m) = List.length l.
induction l; simpl.
reflexivity.
intro m; case m; clear m; simpl.
apply shift_length.
intros m; rewrite IHl; reflexivity.
Qed.

Lemma shift_has_element :
forall l : Rlist, forall cu cur : cursor, forall e : X.element_t,
cur <> cu -> has_element l cur = false ->
has_element (shift l cu e) cur = false.
induction l; simpl; intros cu cur _ Hdiff.
intros _; rewrite Bool.orb_false_r; case_eq (beq_nat cu cur);
[intro Hko; contradict Hdiff|reflexivity]; symmetry; apply beq_nat_true;
exact Hko.
intro Hint; apply Bool.orb_false_elim in Hint; destruct Hint as [Hd Hhe];
rewrite Hd; rewrite Bool.orb_false_l; apply (IHl _ _ _ Hdiff Hhe).
Qed.

Lemma wf_shift :
forall l : Rlist, forall cu : cursor, forall e : X.element_t,
cu > 0 -> has_element l cu = false ->
well_formed l -> well_formed (shift l cu e).
intros l cu; induction l; simpl; intros _ Hcu.
intros _ _; split; [exact Hcu|auto].
intros Hint [Hft[Hhea Hwf]]; apply Bool.orb_false_elim in Hint;
destruct Hint as [Hdiff Hhecu]; apply beq_nat_false in Hdiff.
split; [exact Hft|]; split; [apply (shift_has_element l _ _ _ Hdiff Hhea)
|apply (IHl _ Hcu Hhecu Hwf)].
Qed.

Lemma wf_invalidate :
forall l : Rlist, forall m : nat, well_formed(l) ->
well_formed(invalidate l m).
induction l; simpl.
auto.
intros m [Hfst[Hhe Hwf]]; case m; clear m; simpl.
apply (wf_shift l _ _ Hfst Hhe Hwf).
intros m; split; [exact Hfst|]; split; [|apply (IHl m Hwf)].
generalize m Hhe; clear; induction l; simpl; intro m.
reflexivity.
intro Hint; apply Bool.orb_false_elim in Hint;
destruct Hint as [Hdiff Hhe].
case m; clear m; simpl.
apply beq_nat_false in Hdiff;
apply (shift_has_element); [intro Heq; contradict Hdiff;
symmetry; exact Heq|exact Hhe].
intro m; rewrite Hdiff; rewrite Bool.orb_false_l;
apply (IHl m Hhe).
Qed.

End Shift.

(*** RIGHT ***)

Definition right1 (v : Rlist) (i : Z) :=
let n :=
if (Zgt_bool i 0 && Zge_bool (Z_of_nat (List.length v)) i)%bool then
Zabs_nat i else O in
if beq_nat n O then nil else Shift.invalidate(skipn (pred n) v)  O.

Lemma right1_length :
forall v : Rlist, forall i : Z,
Zge (Z_of_nat (List.length v + 1)) i /\ Zgt i 0 ->
Zplus i (Z_of_nat (List.length (right1 v i))) =
Z_of_nat (List.length v + 1).
intros v i; unfold right1.
generalize (bool_is_valid v i);
case ((Zgt_bool i 0 && Zge_bool (Z_of_nat (List.length v)) i)%bool).
intros [Hli Hpi] _; generalize Hli Hpi;
rewrite <- (Zabs_eq i (Zlt_le_weak _ _ (Zgt_lt _ _ Hpi)));
rewrite <- inj_Zabs_nat; rewrite <- inj_0;
rewrite Zabs_nat_Z_of_nat.
clear; intros Hli Hpi; apply Zge_le in Hli;
apply inj_le_rev in Hli; apply inj_gt_rev in Hpi.
case_eq (beq_nat (Zabs_nat i) 0); simpl.
intro Hko; contradict Hpi; apply beq_nat_true in Hko;
rewrite Hko; apply gt_irrefl.
rewrite <- (firstn_skipn (pred (Zabs_nat i)) v) at 2.
intros _; rewrite app_length; rewrite <- inj_plus; apply inj_eq.
rewrite firstn_length;
rewrite (Min.min_l _ _ (le_trans _ _ _ (le_pred_n _) Hli)).
rewrite <- plus_n_Sm; rewrite <- plus_n_O; rewrite <- plus_Sn_m.
rewrite Shift.invalidate_length;
rewrite <- (S_pred _ O Hpi); reflexivity.
intros [Hko|Hgt] [Hge Hp]; rewrite <- beq_nat_refl;
[contradict Hko; apply Zgt_not_le; exact Hp|].
generalize Hge Hgt; clear Hge Hgt;
rewrite <- (Zabs_eq i (Zlt_le_weak _ _ (Zgt_lt _ _ Hp)));
rewrite <- plus_n_Sm; rewrite <- plus_n_O;
rewrite <- inj_Zabs_nat; intros Hge Hgt.
apply Zge_le in Hge; apply inj_le_rev in Hge;
apply inj_gt_rev in Hgt; rewrite <- inj_plus; simpl List.length;
rewrite <- (plus_n_O (Zabs_nat i)); apply inj_eq.
apply le_lt_eq_dec in Hge; destruct Hge as [Hko|Hex].
contradict Hko; unfold lt; apply gt_not_le; apply gt_n_S; exact Hgt.
exact Hex.
Qed.

Lemma right1_element :
forall v : Rlist, forall i j : Z,
Zge (Z_of_nat (List.length v + 1)) i /\ Zgt i 0 ->
Zlt 0 j /\ Zle j (Z_of_nat (List.length (right1 v i))) ->
element (right1 v i) j = element v (j + i - (Z_of_nat 1)).
unfold element; intros v i j Hi.
generalize (bool_is_valid v (j+i-(Z_of_nat 1)));
case ((Zgt_bool (j+i-(Z_of_nat 1)) 0
&& Zge_bool (Z_of_nat (List.length v)) (j+i-(Z_of_nat 1)))%bool).
generalize (bool_is_valid (right1 v i) j);
case ((Zgt_bool j 0 &&
Zge_bool (Z_of_nat (List.length (right1 v i))) j)%bool).
intros [_ Hjp]; generalize Hjp; rewrite <- inj_0;
rewrite <- (Zabs_eq j (Zlt_le_weak _ _ (Zgt_lt _ _ Hjp))).
rewrite <- inj_Zabs_nat; rewrite Zabs_nat_Z_of_nat;
clear Hjp; intros Hjp [Hlji Hpji] _;
apply inj_gt_rev in Hjp.
case_eq (beq_nat (Zabs_nat j) 0);
[intro Hko; contradict Hjp; apply beq_nat_true in Hko;
rewrite Hko; apply gt_irrefl|intros _; unfold right1].
unfold to_cursor; generalize (bool_is_valid v i);
case ((Zgt_bool i 0 && Zge_bool (Z_of_nat (List.length v)) i)%bool).
intros [Hli Hip]; generalize Hli Hip Hlji Hpji;
rewrite <- (Zabs_eq i (Zlt_le_weak _ _ (Zgt_lt _ _ Hip)));
rewrite <- inj_0 ; rewrite <- inj_Zabs_nat;
clear Hli Hip Hlji Hpji; intros Hli Hip Hlji Hpji; apply inj_gt_rev in Hip;
apply Zge_le in Hli; apply inj_le_rev in Hli;
rewrite Zabs_nat_Z_of_nat. 
case_eq (beq_nat (Zabs_nat i) 0);
[intro Hko; contradict Hip; apply beq_nat_true in Hko;
rewrite Hko; apply gt_irrefl| intros _].
generalize Hlji Hpji; rewrite <- inj_plus; rewrite <- inj_minus1;
[|apply Zgt_lt in Hpji; apply Zlt_0_minus_lt in Hpji;
apply lt_le_weak; rewrite <- inj_plus in Hpji;
apply inj_lt_rev in Hpji; exact Hpji].
clear Hpji Hlji; intros Hlji Hpji; apply Zge_le in Hlji;
apply inj_le_rev in Hlji; apply inj_gt_rev in Hpji;
rewrite Zabs_nat_Z_of_nat.
case_eq (beq_nat (Zabs_nat j + Zabs_nat i - 1) 0);
[intro Hko; contradict Hpji; apply beq_nat_true in Hko;
rewrite Hko; apply gt_irrefl| intros _].
generalize (Zabs_nat i) v (Zabs_nat j) Hjp Hip Hli Hpji Hlji; clear.
induction n; simpl.
intros v m _ Hko; contradict Hko; apply gt_irrefl.
intros v m; case_eq n; simpl; [rewrite plus_comm;
rewrite minus_plus; rewrite Shift.invalidate_element; reflexivity|].
intros nn Hnn; case v; simpl.
rewrite Shift.invalidate_element;
case (pred m); case (pred (m + S (S nn) - 1)); reflexivity.
rewrite <- (plus_n_Sm m); rewrite <- minus_Sn_m;
[rewrite <- pred_Sn|rewrite <- plus_n_Sm; apply gt_le_S; apply gt_Sn_O].
case_eq (m + S nn - 1).
rewrite <- pred_of_minus; rewrite <- plus_n_Sm; rewrite <- pred_Sn.
intros Heq e l Hpm; apply gt_le_S in Hpm;
apply (lt_plus_trans 0 m nn) in Hpm; contradict Hpm;
rewrite Heq; apply lt_irrefl.
intros mm Hmm _ vv; rewrite (pred_Sn nn) at 3; rewrite (pred_Sn mm) at 3;
rewrite <- Hmm; rewrite <- Hnn.
intros Hm _ Hnl _ Hml; generalize (le_S_n _ _ Hml); apply (IHn _ _ Hm);
[rewrite Hnn; apply gt_Sn_O|exact (le_S_n _ _ Hnl)|
rewrite Hnn; rewrite Hmm; apply gt_Sn_O].
intros [Hko |Hlg]; [destruct Hi as [_ Hex]; contradict Hko;
apply Zgt_not_le; exact Hex|rewrite <- beq_nat_refl; simpl].
case(beq_nat (Zabs_nat (Z_of_nat (Zabs_nat j) + i - 1)) 0).
case(pred (Zabs_nat j)); reflexivity.
rewrite nth_overflow; [case(pred (Zabs_nat j)); reflexivity|].
rewrite Zabs_nat_Zminus; [|split; [assert ((1=Z_of_nat 1)%Z); [auto|];
rewrite H; rewrite <- inj_0; apply inj_le; apply le_n_Sn|
apply Zlt_le_weak; apply Zlt_0_minus_lt; apply Zgt_lt; exact Hpji]].
rewrite Zabs_nat_Zplus; [|apply Zlt_le_weak; apply Zgt_lt;
rewrite <- inj_0; apply inj_gt; exact Hjp|apply Zlt_le_weak; apply Zgt_lt;
destruct Hi as [_ Hex]; exact Hex].
destruct Hi as [Hil Hip]; generalize Hil Hip Hlg;
rewrite <- (Zabs_eq i (Zlt_le_weak _ _ (Zgt_lt _ _ Hip))).
rewrite <- inj_Zabs_nat; rewrite Zabs_nat_Z_of_nat;
clear Hil Hip Hlg; intros Hil Hip Hlg.
apply inj_gt_rev in Hlg; apply Zge_le in Hil; apply inj_le_rev in Hil.
rewrite <- plus_n_Sm in Hil; rewrite <- plus_n_O in Hil;
apply gt_le_S in Hlg; rewrite <- (le_antisym _ _ Hlg Hil);
rewrite Zabs_nat_Z_of_nat.
assert ((1=Z_of_nat 1)%Z); [auto|rewrite H; rewrite Zabs_nat_Z_of_nat];
rewrite <- pred_of_minus; rewrite (pred_Sn (List.length v)) at 1;
apply le_pred; apply gt_le_S; apply gt_pred.
generalize (plus_lt_compat_l 0 (Zabs_nat j) (S (List.length v)));
unfold lt; apply gt_le_S in Hjp; rewrite <- plus_n_O.
intro HH; rewrite plus_comm; apply HH in Hjp; apply (le_S_gt _ _ Hjp).
intros [Hko | Hko] _ [Hjp Hji].
apply Zlt_gt in Hjp; contradict Hjp; apply Zle_not_gt; exact Hko.
contradict Hko; apply Zle_not_gt; exact Hji.
intros [Hko|Hko] [Hjp Hl].
apply (Zplus_le_compat_r _ _ (Z_of_nat 1)) in Hko;
rewrite Zplus_comm in Hko; rewrite Zplus_minus in Hko; simpl in Hko.
contradict Hko; apply Zgt_not_le.
destruct Hi as [_ Hip]; apply Zlt_gt; rewrite <- (Zplus_0_r 1);
rewrite (Zplus_comm j); apply Zgt_le_succ in Hip; simpl in Hip.
apply Zplus_le_lt_compat; [exact Hip|exact Hjp].
apply (Zplus_le_compat_l _ _ i) in Hl. rewrite (right1_length v i Hi) in Hl.
contradict Hko; apply Zle_not_gt; apply (Zplus_le_reg_r _ _ (Z_of_nat 1));
rewrite <- inj_plus; rewrite Zplus_comm; rewrite Zplus_minus.
rewrite Zplus_comm; exact Hl.
Qed.

Lemma Wf_right1 :
forall v : list, forall i : Z, well_formed (right1 v i).
intros [v Hwf]; simpl; unfold right1.
intro i;
case ((Zgt_bool i 0 && Zge_bool (Z_of_nat (List.length v)) i)%bool);
[|rewrite <- beq_nat_refl; simpl; auto].
case (beq_nat (Zabs_nat i) 0); [simpl; auto|].
apply Shift.wf_invalidate.
generalize (pred (Zabs_nat i)) Hwf; clear; induction v; simpl.
intro n; case n; simpl; auto.
intro n; case n; clear n; simpl; [auto|intro n].
intros [_[_ Hwf]]; apply (IHv n Hwf).
Qed.

Definition right (v : list) (i : Z) : list :=
Build_list (right1 v i) (Wf_right1 v i).

Lemma right_element :
forall v : list, forall i j : Z,
Zge (Z_of_nat (length v + 1)) i /\ Zgt i 0 ->
Zlt 0 j /\ Zle j (Z_of_nat (length (right v i))) ->
element (right v i) j = element v (j + i - (Z_of_nat 1)).
unfold length; intros [v Hwf]; simpl;
apply right1_element.
Qed.

Lemma right_length :
forall v : list, forall i : Z,
Zge (Z_of_nat (length v + 1)) i /\ Zgt i 0 ->
Zplus i (Z_of_nat (length (right v i))) =
Z_of_nat (length v + 1).
unfold length; intros [v Hwf]; simpl;
apply right1_length.
Qed.

(*** INSERT ***)

Fixpoint insert1 (v : Rlist) (e : X.element_t) (cu : cursor) (n : nat) :=
match n with
O => (cu, e) :: v
| S(m) => match v with
   nil => (cu, e) :: nil
 | a :: vs => a :: (insert1 vs e cu m)
 end
end.

Definition insertl (v : Rlist) (i : Z) (e : X.element_t) : Rlist :=
let n := 
if (Zgt_bool i 0 && Zge_bool (Z_of_nat (List.length v)) i)%bool then
Zabs_nat i else O in
if beq_nat n O then
insert1 v e (New_Max.new v) (List.length v) else
Shift.invalidate (insert1 v e (New_Max.new v) (pred n)) (pred n).

Lemma insert1_length :
forall v : Rlist, forall e : X.element_t, forall cu : nat, forall n : nat,
List.length(insert1 v e cu n) = S(List.length v).
induction v; simpl.
intros e cu n; case n; reflexivity.
intros e cu n; case n; simpl; [|clear n; intro n; rewrite IHv]; reflexivity.
Qed.

Lemma insertl_length :
forall v : Rlist, forall e : X.element_t, forall i : Z,
List.length(insertl v i e) = S(List.length v).
unfold insertl; simpl; intros v e i.
case (beq_nat (if (Zgt_bool i 0 && Zge_bool (Z_of_nat (List.length v)) i)%bool
         then Zabs_nat i
         else 0) 0); [|rewrite Shift.invalidate_length];
apply insert1_length.
Qed.

Lemma insert1_element_new :
forall v : Rlist, forall e : X.element_t, forall cu : cursor,forall n : nat,
n <= List.length v ->
snd(nth n (insert1 v e cu n) (O,X.e_nl)) = e.
induction v; simpl.
intros e cu n; case n; simpl; [reflexivity|].
clear n; intros n Hko; contradict Hko; apply le_Sn_O.
intros e cu n; case n; [reflexivity|].
clear n; intros n Hnn; apply le_S_n in Hnn;
apply (IHv _ _ _ Hnn).
Qed.

Lemma insertl_element_new :
forall v : Rlist, forall e : X.element_t, forall i : Z,
Zge (Z_of_nat (S (List.length v))) i /\ Zgt i 0 ->
element (insertl v i e) i = e.
intros v e i; unfold insertl; unfold element.
generalize (bool_is_valid v i);
case ((Zgt_bool i 0 && Zge_bool (Z_of_nat (List.length v)) i)%bool).
intros [Hil Hpi] Hin;
rewrite <- (insert1_length v e (New_Max.new v) (pred(Zabs_nat i))) in Hin;
rewrite <- (Shift.invalidate_length _ (pred(Zabs_nat i))) in Hin.
case_eq (beq_nat (Zabs_nat i) 0);
[intro Hko; apply beq_nat_true in Hko; destruct Hin as [_ Hpi2];
contradict Hpi2; rewrite <- (Zabs_eq _ (Zlt_le_weak _ _ (Zgt_lt _ _ Hpi)));
rewrite <- inj_Zabs_nat; rewrite Hko; apply Zgt_irrefl|].
rewrite (is_valid_bool_true _ _ Hin); intro Hdiff; rewrite Hdiff.
generalize Hil; rewrite <- (Zabs_eq _ (Zlt_le_weak _ _ (Zgt_lt _ _ Hpi)));
rewrite <- inj_Zabs_nat; rewrite Zabs_nat_Z_of_nat.
clear Hil; intro Hil; apply Zge_le in Hil; apply inj_le_rev in Hil.
rewrite Shift.invalidate_element;
apply insert1_element_new; apply (le_trans _ _ _ (le_pred_n _) Hil).
intros Hi Hin; rewrite <- beq_nat_refl;
rewrite <- (insert1_length v e (New_Max.new v) (List.length v)) in Hin;
rewrite (is_valid_bool_true _ _ Hin).
destruct Hin as [Hil Hpi]; destruct Hi as [Hko|Hgt];
[contradict Hko; apply Zgt_not_le; exact Hpi|
rewrite insert1_length in Hil].
generalize Hgt Hil Hpi;
rewrite <- (Zabs_eq _ (Zlt_le_weak _ _ (Zgt_lt _ _ Hpi)));
rewrite <- inj_Zabs_nat; rewrite Zabs_nat_Z_of_nat.
clear Hgt Hil Hpi; rewrite <- inj_0; intros Hgt Hil Hpi;
apply inj_gt_rev in Hgt; apply Zge_le in Hil;
apply inj_le_rev in Hil; apply inj_gt_rev in Hpi.
case_eq (beq_nat (Zabs_nat i) 0); [intro Hko; apply beq_nat_true in Hko;
contradict Hpi; rewrite Hko; apply gt_irrefl|intros _];
rewrite (le_antisym _ _ Hil (gt_le_S _ _ Hgt)); simpl.
apply insert1_element_new; apply le_refl.
Qed.

Lemma insert1_element_inf :
forall v : Rlist, forall e : X.element_t, forall cu : cursor,
forall m n : nat,
m <= List.length v -> m > n ->
snd(nth n v (O,X.e_nl)) = snd(nth n (insert1 v e cu m) (O,X.e_nl)).
induction v; simpl.
intros e cu m n Hm; rewrite <- (le_n_O_eq _ Hm);
intro Hko; contradict Hko; apply le_not_gt; apply le_O_n.
intros e cu m n; case m; [intros _ Hko; contradict Hko;
apply le_not_gt; apply le_O_n | clear m; intro m; simpl].
case n; simpl; [reflexivity|clear n; intro n].
intros Hl Hgt; apply le_S_n in Hl; apply gt_S_n in Hgt;
apply(IHv _ _ _ _ Hl Hgt).
Qed.

Lemma insertl_element_inf :
forall v : Rlist, forall e : X.element_t, forall i j: Z,
Zge (Z_of_nat (S (List.length v))) i /\ Zgt i 0 ->
Zlt 0 j /\ Zlt j i ->
element v j = element (insertl v i e) j.
intros v e i j; unfold insertl; unfold element.
generalize (bool_is_valid v i);
case ((Zgt_bool i 0 && Zge_bool (Z_of_nat (List.length v)) i)%bool);
intros Hin [Hli Hpi] [Hpj Hji]; apply Zlt_gt in Hpj; apply Zge_le in Hli.
case_eq (beq_nat (Zabs_nat i) 0);
[intro Hko; apply beq_nat_true in Hko; destruct Hin as [_ Hpi2];
contradict Hpi2; rewrite <- (Zabs_eq _ (Zlt_le_weak _ _ (Zgt_lt _ _ Hpi)));
rewrite <- inj_Zabs_nat; rewrite Hko; apply Zgt_irrefl|].
rewrite <- (insert1_length v e (New_Max.new v) (pred (Zabs_nat i))) in Hli;
rewrite <- (Shift.invalidate_length _ (pred(Zabs_nat i))) in Hli;
destruct Hin as [Hlli _]; apply Zge_le in Hlli;
rewrite (is_valid_bool_true v j);[|split;
[exact (Zle_ge _ _ (Zle_trans _ _ _ (Zlt_le_weak _ _ Hji) Hlli))|
exact Hpj]].
rewrite (is_valid_bool_true _ j);
[|split; [exact (Zle_ge _ _ (Zle_trans _ _ _ (Zlt_le_weak _ _ Hji) Hli))|
exact Hpj]].
intros _; generalize Hlli Hpi Hpj Hji;
rewrite <- (Zabs_eq _ (Zlt_le_weak _ _ (Zgt_lt _ _ Hpj)));
rewrite <- inj_Zabs_nat; rewrite Zabs_nat_Z_of_nat;
rewrite <- (Zabs_eq _ (Zlt_le_weak _ _ (Zgt_lt _ _ Hpi)));
rewrite <- inj_Zabs_nat; rewrite Zabs_nat_Z_of_nat.
clear; rewrite <- inj_0; intros Hli Hpi Hpj Hji; apply inj_le_rev in Hli;
apply inj_gt_rev in Hpi; apply inj_gt_rev in Hpj; apply Zlt_gt in Hji;
apply inj_gt_rev in Hji.
case_eq(beq_nat (Zabs_nat j) 0); [intro Hko; contradict Hpj;
apply beq_nat_true in Hko; rewrite Hko; apply gt_irrefl|intros _].
rewrite (S_pred _ _ Hpi) in Hli; rewrite (S_pred _ _ Hpi) in Hji;
rewrite (S_pred _ _ Hpj) in Hji; apply gt_S_n in Hji;
apply lt_le_weak in Hli.
rewrite Shift.invalidate_element;
apply (insert1_element_inf _ _ _ _ _ Hli Hji).
rewrite <- beq_nat_refl.
generalize (Zle_gt_trans _ _ _ Hli (Zlt_gt _ _ Hji)); intro Hlli;
rewrite <- (insert1_length v e (New_Max.new v) (List.length v)) in Hli;
rewrite (is_valid_bool_true 
(insert1 v e (New_Max.new v) (List.length v)) j); [|split;
[exact (Zle_ge _ _ (Zle_trans _ _ _ (Zlt_le_weak _ _ Hji) Hli))|
exact Hpj]];
rewrite (insert1_length v e (New_Max.new v) (List.length v)) in Hli.
rewrite inj_S in Hlli; apply Zgt_succ_le in Hlli;
rewrite (is_valid_bool_true v j);[|split;
[exact (Zle_ge _ _ Hlli)|exact Hpj]].
destruct Hin as [Hko|Hgt]; [contradict Hko; apply Zgt_not_le; exact Hpi|].
generalize Hpj Hji; rewrite inj_S in Hli;
rewrite (Zle_antisym _ _ Hli (Zgt_le_succ _ _ Hgt)); rewrite <- inj_S.
rewrite <- (Zabs_eq _ (Zlt_le_weak _ _ (Zgt_lt _ _ Hpj)));
rewrite <- inj_Zabs_nat; rewrite Zabs_nat_Z_of_nat.
clear; rewrite <- inj_0; intros Hpj Hji;
apply inj_gt_rev in Hpj; apply Zlt_gt in Hji; apply inj_gt_rev in Hji.
case_eq(beq_nat (Zabs_nat j) 0); [intro Hko; contradict Hpj;
apply beq_nat_true in Hko; rewrite Hko; apply gt_irrefl|intros _].
rewrite (S_pred _ _ Hpj) in Hji; apply gt_S_n in Hji.
apply (insert1_element_inf _ _ _ _ _ (le_refl _) Hji).
Qed.

Lemma insert1_element_sup :
forall v : Rlist, forall e : X.element_t, forall cu : cursor,
 forall m n : nat,
n > m -> n <= List.length v ->
snd(nth (pred n) v (O,X.e_nl)) = snd(nth n (insert1 v e cu m) (O,X.e_nl)).
induction v; simpl.
intros e cu m n Hnm Hm; rewrite <- (le_n_O_eq _ Hm) in Hnm;
contradict Hnm; apply le_not_gt; apply le_O_n.
intros e cu m n; case m; simpl.
case n; [intro Hko; contradict Hko; apply gt_irrefl|intro nn;
case nn; reflexivity].
clear m; intro m; case n; simpl; [reflexivity|clear n; intro n].
case n; [intros Hko; apply gt_S_n in Hko; contradict Hko;
apply le_not_gt; apply le_O_n|clear n; intro n].
rewrite (pred_Sn n) at 3;
intros Hnm Hnl; apply gt_S_n in Hnm; apply le_S_n in Hnl;
apply (IHv _ _ _ _ Hnm Hnl); apply gt_Sn_O.
Qed.

Lemma insertl_element_sup :
forall v : Rlist, forall e : X.element_t, forall i j: Z,
Zge (Z_of_nat (S (List.length v))) i /\ Zgt i 0 ->
Zlt i j /\ Zle j (Z_of_nat (S (List.length v))) ->
element v (j - Z_of_nat 1) = element (insertl v i e) j.
intros v e i j; unfold insertl; unfold element.
generalize (bool_is_valid v i);
case ((Zgt_bool i 0 && Zge_bool (Z_of_nat (List.length v)) i)%bool);
intros Hin [Hli Hpi] [Hji Hlj]; apply Zlt_gt in Hji; apply Zge_le in Hli.
case_eq (beq_nat (Zabs_nat i) 0);
[intro Hko; apply beq_nat_true in Hko; destruct Hin as [_ Hpi2];
contradict Hpi2; rewrite <- (Zabs_eq _ (Zlt_le_weak _ _ (Zgt_lt _ _ Hpi)));
rewrite <- inj_Zabs_nat; rewrite Hko; apply Zgt_irrefl|].
destruct Hin as [Hlli _]; apply Zge_le in Hlli;
rewrite (is_valid_bool_true v _);
[|rewrite inj_S; rewrite Zminus_succ_r; rewrite Zminus_0_r;
rewrite (Zsucc_pred j) in Hlj; rewrite inj_S in Hlj;
apply Zgt_le_succ in Hpi; split ; [ apply Zle_ge;
apply (Zsucc_le_reg _ _ Hlj)|apply Zgt_succ_pred;
apply (Zgt_le_trans _ _ _ Hji Hpi)]].
rewrite <- (insert1_length v e (New_Max.new v) (pred (Zabs_nat i))) in Hlj;
rewrite <- (Shift.invalidate_length _ (pred (Zabs_nat i))) in Hlj;
rewrite (is_valid_bool_true _ j);[|split;
[exact (Zle_ge _ _ Hlj)|exact (Zgt_trans _ _ _ Hji Hpi)]];
rewrite (Shift.invalidate_length _ (pred (Zabs_nat i))) in Hlj;
rewrite (insert1_length v e (New_Max.new v) (pred (Zabs_nat i))) in Hlj.
intros _; generalize Hlli Hpi Hji Hlj;
rewrite <- (Zabs_eq _ (Zlt_le_weak _ _ (Zgt_lt _ _
(Zgt_trans _ _ _ Hji Hpi))));
rewrite <- inj_Zabs_nat; rewrite Zabs_nat_Z_of_nat;
rewrite <- (Zabs_eq _ (Zlt_le_weak _ _ (Zgt_lt _ _ Hpi)));
rewrite <- inj_Zabs_nat.
clear; rewrite <- inj_0; intros Hli Hpi Hji Hlj; apply inj_le_rev in Hli;
apply inj_gt_rev in Hpi; apply inj_gt_rev in Hji; apply inj_le_rev in Hlj.
rewrite <- inj_minus1; [|apply gt_le_S; apply (gt_trans _ _ _ Hji Hpi)].
repeat(rewrite Zabs_nat_Z_of_nat).
case_eq(beq_nat (Zabs_nat j) 0); [intro Hko; contradict Hji;
apply beq_nat_true in Hko; rewrite Hko; apply gt_asym; exact Hpi|intros _].
generalize (gt_trans _ _ _ Hji Hpi); intro Hpj;
rewrite <- pred_of_minus; apply gt_le_S in Hji;
apply le_pred in Hji; rewrite <- pred_Sn in Hji.
case_eq(beq_nat (pred(Zabs_nat j)) 0);[intro Hko; contradict Hji;
apply beq_nat_true in Hko; rewrite Hko; apply gt_not_le; exact Hpi|
intros _].
generalize (le_gt_trans _ _ _ Hji Hpi); intro Hppj;
apply le_n_S in Hji; rewrite <- (S_pred _ _ Hpj) in Hji;
rewrite (S_pred _ _ Hpi) in Hji; apply lt_pred in Hji;
apply le_S_gt in Hji.
apply le_pred in Hlj; rewrite <- pred_Sn in Hlj.
rewrite (Shift.invalidate_element _ _);
apply (insert1_element_sup _ _ _ _ _ Hji Hlj).
rewrite <- beq_nat_refl.
rewrite (is_valid_bool_true v _);
[|rewrite inj_S; rewrite Zminus_succ_r; rewrite Zminus_0_r;
rewrite (Zsucc_pred j) in Hlj; rewrite inj_S in Hlj;
apply Zgt_le_succ in Hpi; split ; [ apply Zle_ge;
apply (Zsucc_le_reg _ _ Hlj)|apply Zgt_succ_pred;
apply (Zgt_le_trans _ _ _ Hji Hpi)]].
rewrite <- (insert1_length v e (New_Max.new v) (List.length v)) in Hlj;
rewrite (is_valid_bool_true _ j);[|split;
[exact (Zle_ge _ _ Hlj)|exact (Zgt_trans _ _ _ Hji Hpi)]];
rewrite (insert1_length v e (New_Max.new v) (List.length v)) in Hlj.
destruct Hin as [Hko|Hgt]; [contradict Hko; apply Zgt_not_le; exact Hpi|].
contradict Hlj; apply Zgt_not_le; rewrite inj_S in Hli; rewrite inj_S;
rewrite (Zle_antisym _ _ (Zgt_le_succ _ _ Hgt) Hli); exact Hji.
Qed.

Lemma insert1_to_index :
forall v : Rlist, forall cu cnew : cursor, forall i n : nat,
forall e : X.element_t,
i <= List.length v ->
to_index1 v cu n > 0 ->
i + n > to_index1 v cu n ->
to_index1 v cu n = to_index1 (insert1 v e cnew i) cu n.
intros v cu cnew; induction v; simpl.
intros i n e _ Hko; contradict Hko; apply gt_irrefl.
intros i n e; case i; clear i; simpl.
case (beq_nat cu (fst a)).
intros _ _ Hko; contradict Hko; apply gt_irrefl.
intros _ Hp Hko; contradict Hko; apply le_not_gt;
apply lt_le_weak; apply to_index1_sup; exact Hp.
intros i Hil; case (beq_nat cu (fst a)).
reflexivity.
rewrite plus_n_Sm; apply le_S_n in Hil; apply (IHv i (S n) e Hil).
Qed.

Lemma insert1_to_index_inv :
forall v : Rlist, forall cu cnew : cursor, forall i n : nat,
forall e : X.element_t,
i <= List.length v ->
to_index1 (insert1 v e cnew i) cu n > 0 ->
i + n > to_index1 (insert1 v e cnew i) cu n ->
to_index1 v cu n = to_index1 (insert1 v e cnew i) cu n.
intros v cu cnew; induction v; simpl.
intros i n e Hi; apply le_n_O_eq in Hi; rewrite <- Hi; simpl.
case (beq_nat cu cnew); [intros _ Hko|intros Hko];
contradict Hko; apply gt_irrefl.
intros i n e; case i; clear i; simpl.
case (beq_nat cu (fst a)).
intros _ _ Hko; contradict Hko; case (beq_nat cu cnew);
[apply gt_irrefl|apply le_not_gt; apply le_n_Sn].
case (beq_nat cu cnew).
intros _ _ Hko; contradict Hko; apply gt_irrefl.
intros _ Hp Hko; contradict Hko; apply le_not_gt;
apply lt_le_weak; apply lt_le_weak; apply to_index1_sup; exact Hp.
intros i Hil; case (beq_nat cu (fst a)).
reflexivity.
rewrite plus_n_Sm; apply le_S_n in Hil; apply (IHv i (S n) e Hil).
Qed.

Lemma insertl_to_index :
forall v : Rlist, forall i : Z, forall cu : cursor, forall e : X.element_t,
Zge (Z_of_nat (S(List.length v))) i /\ Zgt i 0 ->
(Zlt 0 (to_index v cu) /\ Zlt (to_index v cu) i \/
(Zlt 0 (to_index (insertl v i e) cu) /\
Zlt (to_index (insertl v i e) cu) i) ->
to_index v cu = to_index (insertl v i e) cu).
unfold to_index; unfold insertl;
intros v i cu e [Hli Hip].
generalize (bool_is_valid v i);
case ((Zgt_bool i 0 && Zge_bool (Z_of_nat (List.length v)) i)%bool).
rewrite <- (Zabs_eq i (Zlt_le_weak _ _ (Zgt_lt _ _ Hip))).
rewrite <- inj_0; rewrite <- inj_Zabs_nat; rewrite Zabs_nat_Z_of_nat;
intros [Hil Hipp]; apply Zge_le in Hil;
apply inj_le_rev in Hil; apply inj_gt_rev in Hipp.
case_eq(beq_nat (Zabs_nat i) 0); 
[intro Hko; apply beq_nat_true in Hko; contradict Hipp;
rewrite Hko; apply gt_irrefl|intros _].
rewrite (S_pred _ _ Hipp) in Hil; apply lt_le_weak in Hil.
intros [[Hgt Hle]|[Hgt Hle]]; apply Zlt_gt in Hgt;
apply Zlt_gt in Hle; apply inj_gt_rev in Hgt; apply inj_gt_rev in Hle;
rewrite (S_pred _ _ Hipp) in Hle at 1; apply inj_eq;
rewrite (plus_n_O (pred (Zabs_nat i))) in Hle at 1;
rewrite plus_n_Sm in Hle.
rewrite Shift.invalidate_to_index; rewrite <- (insert1_to_index v _ _ _ _ _
Hil Hgt Hle); [reflexivity|left; split; [exact Hgt|exact Hle]].
generalize Hgt Hle; rewrite Shift.invalidate_to_index.
clear Hgt Hle; intros Hgt Hle.
apply (insert1_to_index_inv v _ _ _ _ _ Hil Hgt Hle).
right; split; [exact Hgt|exact Hle].
rewrite <- beq_nat_refl.
intros [Hko|Hil]; [contradict Hko; apply Zgt_not_le; exact Hip|].
apply Zge_le in Hli; apply Zgt_le_succ in Hil; rewrite <- inj_S in Hil.
rewrite (Zle_antisym _ _ Hli Hil); rewrite <- inj_0.
clear; intros [[Hgt Hle]|[Hgt Hle]];  apply Zlt_gt in Hgt;
apply Zlt_gt in Hle; apply inj_gt_rev in Hgt; apply inj_gt_rev in Hle;
apply inj_eq; rewrite (plus_n_O (List.length v)) in Hle at 1;
rewrite plus_n_Sm in Hle at 1.
apply
(insert1_to_index v _ _ _ _ _ (le_refl (List.length v)) Hgt Hle).
apply
(insert1_to_index_inv v _ _ _ _ _ (le_refl (List.length v)) Hgt Hle).
Qed.

Lemma WF_insert1 :
forall v : Rlist, forall cu : cursor, forall e : X.element_t,
forall n : nat, cu > 0 -> has_element v cu = false ->
well_formed v -> well_formed (insert1 v e cu n).
intros v cu e; induction v; simpl.
intro n; case n; clear n; simpl; [|intros _]; intros Hcu; intros;
split; [exact Hcu|auto|exact Hcu|auto].
intros n Hcu Hint [Hfst[Hhe Hwf]]; case n; clear n; simpl.
split; [exact Hcu|]; split; [exact Hint|];
split; [exact Hfst|]; split; [exact Hhe|exact Hwf].
apply Bool.orb_false_elim in Hint; destruct Hint as [Hdiff Hhecu];
intros n; split; [exact Hfst|]; split; [|apply (IHv n Hcu Hhecu Hwf)].
apply beq_nat_false in Hdiff;
generalize Hdiff Hhe n; clear; induction v; simpl.
intros Hdiff _ n; case n; simpl; [|intros _]; rewrite Bool.orb_false_r.
case_eq (beq_nat cu (fst a)); [intro Hko|reflexivity]; contradict Hdiff;
symmetry; apply beq_nat_true; exact Hko.
case_eq (beq_nat cu (fst a)); [intro Hko|reflexivity]; contradict Hdiff;
symmetry; apply beq_nat_true; exact Hko.
intros Hdiff Hint n; case n; simpl.
rewrite Hint; rewrite Bool.orb_false_r;
case_eq (beq_nat cu (fst a)); [intro Hko|reflexivity]; contradict Hdiff;
symmetry; apply beq_nat_true; exact Hko.
clear n; intro n; apply Bool.orb_false_elim in Hint;
destruct Hint as [Haa0 Hhe]; rewrite Haa0; rewrite Bool.orb_false_l;
apply (IHv Hdiff Hhe).
Qed.

Lemma WF_insertl :
forall v : list, forall i : Z, forall e : X.element_t,
well_formed (insertl v i e).
intros [v Hwf]; simpl; unfold insertl.
intro i;
case ((Zgt_bool i 0 && Zge_bool (Z_of_nat (List.length v)) i)%bool);
[|rewrite <- beq_nat_refl; simpl; auto].
intro e;
case (beq_nat (Zabs_nat i) 0).
apply WF_insert1; [apply New_Max.new_valid|apply New_Max.new_has_element|
exact Hwf].
apply Shift.wf_invalidate.
apply WF_insert1; [apply New_Max.new_valid|apply New_Max.new_has_element|
exact Hwf].
intros e; apply WF_insert1; [apply New_Max.new_valid
|apply New_Max.new_has_element| exact Hwf].
Qed.

Definition insert (v : list) (i : Z) (e : X.element_t) : list :=
Build_list (insertl v i e) (WF_insertl v i e).

Lemma insert_element_inf :
forall v : list, forall e : X.element_t, forall i j: Z,
Zge (Z_of_nat (S (length v))) i /\ Zgt i 0 ->
Zlt 0 j /\ Zlt j i ->
element v j = element (insert v i e) j.
unfold length; intros [v Hwf]; simpl;
apply insertl_element_inf.
Qed.

Lemma insert_element_new :
forall v : list, forall e : X.element_t, forall i : Z,
Zge (Z_of_nat (S (length v))) i /\ Zgt i 0 ->
element (insert v i e) i = e.
unfold length; intros [v Hwf]; simpl;
apply insertl_element_new.
Qed.

Lemma insert_length :
forall v : list, forall e : X.element_t, forall i : Z,
length(insert v i e) = S(length v).
unfold length; intros [v Hwf]; simpl;
apply insertl_length.
Qed.

Lemma insert_element_sup :
forall v : list, forall e : X.element_t, forall i j: Z,
Zge (Z_of_nat (S (length v))) i /\ Zgt i 0 ->
Zlt i j /\ Zle j (Z_of_nat (S (length v))) ->
element v (j - Z_of_nat 1) = element (insert v i e) j.
unfold length; intros [v Hwf]; simpl;
apply insertl_element_sup.
Qed.

Lemma insert_to_index :
forall v : list, forall i : Z, forall cu : cursor, forall e : X.element_t,
Zge (Z_of_nat (S(length v))) i /\ Zgt i 0 ->
(Zlt 0 (to_index v cu) /\ Zlt (to_index v cu) i \/
(Zlt 0 (to_index (insert v i e) cu) /\
Zlt (to_index (insert v i e) cu) i) ->
to_index v cu = to_index (insert v i e) cu).
unfold length; intros [v Hwf]; simpl;
apply insertl_to_index.
Qed.

(*** DELETE ***)

Module Delete (I : Invalidate).

Fixpoint delete1 (v : Rlist) (n : nat) : Rlist :=
match v with
nil => nil
| (a :: ls) => match n with
                O => ls 
               | S m => (a :: (delete1 ls m))
               end
end.

Definition delete (v : Rlist) (i : Z) : Rlist :=
let n := 
if (Zgt_bool i 0 && Zge_bool (Z_of_nat (List.length v)) i)%bool then
Zabs_nat i else O in
if beq_nat n O then v else
I.invalidate (delete1 v (pred n)) (pred n).

Lemma delete1_length :
forall v : Rlist, forall n : nat,
List.length v > n ->
List.length v = S (List.length (delete1 v n)).
induction v; simpl.
intros n Hko; contradict Hko; apply le_not_gt; apply le_O_n.
intros n; case n; [reflexivity|].
clear n; intros n Hl; apply gt_S_n in Hl; 
rewrite (IHv n Hl); reflexivity.
Qed.

Lemma delete_length :
forall v : Rlist, forall i : Z,
Zge (Z_of_nat (List.length v)) i /\ Zgt i 0 ->
List.length v = S (List.length (delete v i)).
intros v i Hin; unfold delete; unfold to_cursor;
rewrite (is_valid_bool_true _ _ Hin).
destruct Hin as [Hli Hpi]; generalize Hli Hpi;
rewrite <- (Zabs_eq _ (Zlt_le_weak _ _ (Zgt_lt _ _ Hpi)));
rewrite <- inj_Zabs_nat; rewrite Zabs_nat_Z_of_nat.
rewrite <- inj_0; clear; intros Hli Hpi; apply Zge_le in Hli;
apply inj_le_rev in Hli; apply inj_gt_rev in Hpi.
case_eq (beq_nat (Zabs_nat i) 0); [intro Heq; contradict Hpi;
apply beq_nat_true in Heq; rewrite Heq; apply gt_irrefl|intros _].
rewrite (S_pred _ _ Hpi) in Hli; apply le_S_gt in Hli.
rewrite I.invalidate_length;
apply delete1_length; exact Hli.
Qed.

Lemma delete1_element_sup :
forall v : Rlist, forall n m : nat,
n > m ->
snd(nth n v (O, X.e_nl)) = snd(nth (pred n) (delete1 v m) (O,X.e_nl)).
induction v; simpl.
intros n m; case n; [reflexivity|]; intro nn; case nn; reflexivity.
intros n m; case n;
[intro Hko; contradict Hko; apply le_not_gt; apply le_O_n|clear n; intro n].
case m; [reflexivity| clear m; intro m; simpl].
case_eq n; [intros _ Hko; contradict Hko; apply le_not_gt;
apply le_n_S; apply le_O_n|intros nn Hnn].
rewrite (pred_Sn nn) at 3; rewrite <- Hnn; intros H;
apply gt_S_n in H; apply (IHv _ _ H).
Qed.

Lemma delete_element_sup :
forall v : Rlist, forall i j : Z,
Zge (Z_of_nat (List.length v)) i /\ Zgt i 0 ->
Zgt (Z_of_nat (List.length v)) j /\ Zge j i ->
element v (j + Z_of_nat 1) = element (delete v i) j.
intros v i j Hin; unfold element; unfold delete;
rewrite (is_valid_bool_true _ _ Hin).
destruct Hin as [Hli Hpi]; intros [Hlj Hji];
generalize (Zle_gt_trans _ _ _ (Zge_le _ _ Hji) Hpi); intro Hpj.
generalize Hli Hpi Hji;
rewrite <- (Zabs_eq _ (Zlt_le_weak _ _ (Zgt_lt _ _ Hpi)));
rewrite <- inj_Zabs_nat; rewrite Zabs_nat_Z_of_nat.
rewrite <- inj_0; clear Hli Hpi Hji; intros Hli Hpi Hji;
apply Zge_le in Hli; apply inj_le_rev in Hli; apply inj_gt_rev in Hpi.
case_eq (beq_nat (Zabs_nat i) 0); [intro Hko; apply beq_nat_true in Hko;
contradict Hpi; rewrite Hko; apply gt_irrefl|intros _].
rewrite (S_pred _ _ Hpi) in Hli; apply le_S_gt in Hli; rewrite inj_0.
rewrite (delete1_length _ _ Hli) in Hlj;
rewrite <- (I.invalidate_length _ (pred (Zabs_nat i))) in Hlj;
rewrite inj_S in Hlj; apply Zgt_succ_le in Hlj.
rewrite (is_valid_bool_true _ j);
[|split; [apply Zle_ge; exact Hlj|exact Hpj]].
generalize Hlj Hpj Hji;
rewrite <- (Zabs_eq _ (Zlt_le_weak _ _ (Zgt_lt _ _ Hpj)));
rewrite <- inj_Zabs_nat; rewrite Zabs_nat_Z_of_nat.
rewrite <- inj_0; clear Hlj Hpj Hji; intros Hlj Hpj Hji;
apply inj_le_rev in Hlj; apply inj_gt_rev in Hpj; apply Zge_le in Hji;
apply inj_le_rev in Hji; rewrite <- inj_plus.
apply le_n_S in Hlj; rewrite I.invalidate_length  in Hlj;
rewrite <- (delete1_length _ _ Hli) in Hlj;
rewrite <- plus_n_Sm; rewrite <- plus_n_O.
rewrite inj_0; rewrite (is_valid_bool_true v (Z_of_nat (S (Zabs_nat j))));
[|split; [apply Zle_ge; apply inj_le; exact Hlj|rewrite <- inj_0;
apply inj_gt; apply gt_Sn_O]]; rewrite Zabs_nat_Z_of_nat.
case_eq (beq_nat (Zabs_nat j) 0); [intro Hko; apply beq_nat_true in Hko;
contradict Hpj; rewrite Hko; apply gt_irrefl|intros _].
case_eq (beq_nat (S(Zabs_nat j)) 0); [intro Hko; apply beq_nat_true in Hko;
symmetry in Hko; contradict Hko; apply O_S|intros _; rewrite <- pred_Sn].
rewrite (S_pred _ _ Hpi) in Hji; apply le_S_gt in Hji.
rewrite I.invalidate_element;
apply (delete1_element_sup v _ _ Hji).
Qed.

Lemma delete1_element_inf :
forall v : Rlist, forall n m : nat,
n > m ->
snd(nth m (delete1 v n) (O,X.e_nl)) = snd(nth m v (O,X.e_nl)).
induction v; simpl; [reflexivity|].
intros n m; case n; [intro Hko; contradict Hko; apply le_not_gt;
apply le_O_n|clear n; intro n].
case m; [simpl; reflexivity|clear m; intro m; simpl].
intro H; apply gt_S_n in H; apply (IHv n m H).
Qed.

Lemma delete_element_inf :
forall v : Rlist, forall i j : Z,
Zge (Z_of_nat (List.length v)) i /\ Zgt i 0 ->
Zlt 0 j /\ Zlt j i ->
element (delete v i) j = element v j.
intros v i j Hin; unfold element; unfold delete; unfold to_cursor;
rewrite (is_valid_bool_true _ _ Hin).
destruct Hin as [Hli Hpi]; intros [Hpj Hji].
generalize (Zle_gt_trans _ _ _ (Zge_le _ _ Hli) (Zlt_gt _ _ Hji));
intro Hlj; generalize Hli Hpi Hji;
rewrite <- (Zabs_eq _ (Zlt_le_weak _ _ (Zgt_lt _ _ Hpi)));
rewrite <- inj_Zabs_nat; rewrite Zabs_nat_Z_of_nat.
rewrite <- inj_0; clear Hli Hpi Hji; intros Hli Hpi Hji;
apply Zge_le in Hli; apply inj_le_rev in Hli; apply inj_gt_rev in Hpi.
case_eq (beq_nat (Zabs_nat i) 0); [intro Hko; apply beq_nat_true in Hko;
contradict Hpi; rewrite Hko; apply gt_irrefl|intros _].
rewrite (S_pred _ _ Hpi) in Hli; apply le_S_gt in Hli.
rewrite inj_0; rewrite (is_valid_bool_true v j);
[|split; [apply Zle_ge; apply Zlt_le_weak; apply Zgt_lt; exact Hlj|
apply Zlt_gt; exact Hpj]].
rewrite (delete1_length _ _ Hli) in Hlj;
rewrite <- (I.invalidate_length _ (pred (Zabs_nat i))) in Hlj;
rewrite inj_S in Hlj; apply Zgt_succ_le in Hlj.
rewrite (is_valid_bool_true _ j);
[|split; [apply Zle_ge; exact Hlj|apply Zlt_gt; exact Hpj]].
generalize Hji Hpj;
rewrite <- (Zabs_eq _ (Zlt_le_weak _ _ (Zgt_lt _ _ (Zlt_gt _ _ Hpj))));
rewrite <- inj_Zabs_nat; rewrite Zabs_nat_Z_of_nat.
clear Hji Hpj Hlj; intros Hji Hpj;
rewrite <- inj_0 in Hpj; apply Zlt_gt in Hpj; apply inj_gt_rev in Hpj;
apply Zlt_gt in Hji; apply inj_gt_rev in Hji.
case_eq (beq_nat (Zabs_nat j) 0); [intro Heq; contradict Hpj;
apply beq_nat_true in Heq; rewrite Heq; apply gt_irrefl|intros _].
rewrite (S_pred _ _ Hpi) in Hji; rewrite (S_pred _ _ Hpj) in Hji;
apply gt_S_n in Hji.
rewrite I.invalidate_element;
apply (delete1_element_inf v _ _ Hji).
Qed.

Lemma WF_delete1 :
forall v : Rlist, forall n : nat,
well_formed v -> well_formed (delete1 v n).
induction v; simpl.
auto.
intros n [Hfst[Hhe Hwf]]; case n; clear n; simpl.
exact Hwf.
intro n; split; [exact Hfst|]; split; [|apply (IHv n Hwf)].
generalize (fst a) n Hhe; intro cu; clear; induction v; simpl.
reflexivity.
intros n Hint; apply Bool.orb_false_elim in Hint;
destruct Hint as [Hdiff Hhe].
case n; clear n; simpl.
exact Hhe.
intro n; rewrite Hdiff; rewrite Bool.orb_false_l;
apply (IHv n Hhe).
Qed.

Lemma WF_delete :
forall v : list, forall i : Z,
well_formed (delete v i).
intros [v Hwf]; simpl; unfold delete.
intro i;
case ((Zgt_bool i 0 && Zge_bool (Z_of_nat (List.length v)) i)%bool);
[|rewrite <- beq_nat_refl; simpl; auto].
case (beq_nat (Zabs_nat i) 0).
exact Hwf.
apply I.wf_invalidate.
apply WF_delete1; exact Hwf.
Qed.

Lemma delete1_to_index :
forall v : Rlist, forall cu : cursor, forall n i : nat,
to_index1 v cu n > 0 -> i + n > to_index1 v cu n ->
to_index1 v cu n = to_index1 (delete1 v i) cu n.
intros v cu; induction v; simpl.
intros n i Hko; contradict Hko; apply gt_irrefl.
intros n i; case i; simpl; clear i.
case (beq_nat cu (fst a)).
intros _ Hko; contradict Hko; apply gt_irrefl.
intros Hp Hko; contradict Hko; apply le_not_gt;
apply lt_le_weak; apply (to_index1_sup _ _ _ Hp).
intro i; case (beq_nat cu (fst a)).
reflexivity.
rewrite plus_n_Sm; apply IHv.
Qed.

Lemma delete1_to_index_inv :
forall v : Rlist, forall cu : cursor, forall n i : nat,
to_index1 (delete1 v i) cu n > 0 ->
i + n > to_index1 (delete1 v i) cu n ->
to_index1 v cu n = to_index1 (delete1 v i) cu n.
intros v cu; induction v; simpl.
intros n i Hko; contradict Hko; apply gt_irrefl.
intros n i; case i; simpl; clear i.
intros Hp Hko; contradict Hko; apply le_not_gt;
apply (to_index1_sup _ _ _ Hp).
intro i; case (beq_nat cu (fst a)).
reflexivity.
rewrite plus_n_Sm; apply IHv.
Qed.

Lemma delete_to_index :
forall v : Rlist, forall i : Z, forall cu : cursor,
Zge (Z_of_nat (List.length v)) i /\ Zgt i 0 ->
(Zlt 0 (to_index v cu) /\ Zlt (to_index v cu) i \/
Zlt 0 (to_index (delete v i) cu) /\ Zlt (to_index (delete v i) cu) i) ->
to_index v cu = to_index (delete v i) cu.
unfold to_index; unfold delete;
intros v i cu Hin; rewrite (is_valid_bool_true _ _ Hin).
destruct Hin as [Hli Hpi]; generalize Hli Hpi;
rewrite <- (Zabs_eq _ (Zlt_le_weak _ _ (Zgt_lt _ _ Hpi)));
rewrite <- inj_Zabs_nat; rewrite Zabs_nat_Z_of_nat;
rewrite <- inj_0; clear Hli Hpi; intros Hli Hpi;
apply Zge_le in Hli; apply inj_le_rev in Hli; apply inj_gt_rev in Hpi.
case_eq (beq_nat (Zabs_nat i) 0); [intro Heq; contradict Hpi;
apply beq_nat_true in Heq; rewrite Heq; apply gt_irrefl|intros _].
rewrite (S_pred _ _ Hpi) in Hli; apply le_S_gt in Hli.
intros [[Hgt Hle]|[Hgt Hle]]; apply Zlt_gt in Hgt;
apply Zlt_gt in Hle; apply inj_gt_rev in Hgt; apply inj_gt_rev in Hle;
rewrite (S_pred _ _ Hpi) in Hle at 1; apply inj_eq;
rewrite (plus_n_O (pred (Zabs_nat i))) in Hle at 1;
rewrite plus_n_Sm in Hle.
rewrite I.invalidate_to_index;
rewrite <- (delete1_to_index _ _ _ _ Hgt Hle); [reflexivity|left].
split; [exact Hgt|exact Hle].
generalize Hgt Hle; rewrite I.invalidate_to_index;
[|right; split; [exact Hgt|exact Hle]].
clear Hgt Hle; intros Hgt Hle;
apply (delete1_to_index_inv _ _ _ _ Hgt Hle).
Qed.

End Delete.

Module Del := Delete(Shift).

Definition delete (v : list) (i : Z) : list :=
Build_list (Del.delete v i) (Del.WF_delete v i).

Lemma delete_length :
forall v : list, forall i : Z,
Zge (Z_of_nat (length v)) i /\ Zgt i 0 ->
length v = S (length (delete v i)).
unfold length; intros [v Hwf]; simpl;
apply Del.delete_length.
Qed.

Lemma delete_element_sup :
forall v : list, forall i j : Z,
Zge (Z_of_nat (length v)) i /\ Zgt i 0 ->
Zgt (Z_of_nat (length v)) j /\ Zge j i ->
element v (j + Z_of_nat 1) = element (delete v i) j.
unfold length; intros [v Hwf]; simpl;
apply Del.delete_element_sup.
Qed.

Lemma delete_element_inf :
forall v : list, forall i j : Z,
Zge (Z_of_nat (length v)) i /\ Zgt i 0 ->
Zlt 0 j /\ Zlt j i ->
element (delete v i) j = element v j.
unfold length; intros [v Hwf]; simpl;
apply Del.delete_element_inf.
Qed.

Lemma delete_to_index :
forall v : list, forall i : Z, forall cu : cursor,
Zge (Z_of_nat (length v)) i /\ Zgt i 0 ->
(Zlt 0 (to_index v cu) /\ Zlt (to_index v cu) i \/
Zlt 0 (to_index (delete v i) cu) /\ Zlt (to_index (delete v i) cu) i) ->
to_index v cu = to_index (delete v i) cu.
unfold length; intros [v Hwf]; simpl;
apply Del.delete_to_index.
Qed.

(*** REPLACE ***)

Fixpoint replace1 (v : Rlist) (e : X.element_t) (n : nat) : Rlist :=
match v with
nil => nil
| (a :: ls) => match n with
                O => ((fst a,e) :: ls) 
               | S m => (a :: (replace1 ls e m))
               end
end.

Definition replace_lst (v : Rlist) (i : Z) (e : X.element_t) : Rlist :=
let n := 
if (Zgt_bool i 0 && Zge_bool (Z_of_nat (List.length v)) i)%bool then
Zabs_nat i else O in
if beq_nat n O then v else replace1 v e (pred n).

Lemma WF_replace1 :
forall v : Rlist, forall e : X.element_t, forall n : nat,
well_formed v -> well_formed (replace1 v e n).
intros v e; induction v; simpl.
auto.
intros n [Hfst[Hhe Hwf]]; case n; clear n; simpl.
split; [exact Hfst|]; split; [exact Hhe|exact Hwf].
intro n; split; [exact Hfst|]; split; [|apply (IHv n Hwf)].
generalize n Hhe; clear; induction v; simpl.
reflexivity.
intros n Hint; apply Bool.orb_false_elim in Hint;
destruct Hint as [Hdiff Hhe].
case n; clear n; simpl.
rewrite Hdiff; rewrite Bool.orb_false_l; exact Hhe.
intro n; rewrite Hdiff; rewrite Bool.orb_false_l;
apply (IHv n Hhe).
Qed.

Lemma WF_replace :
forall v : list, forall i : Z, forall e : X.element_t,
well_formed (replace_lst v i e).
intros [v Hwf]; simpl; unfold replace_lst.
intro i;
case ((Zgt_bool i 0 && Zge_bool (Z_of_nat (List.length v)) i)%bool);
[|rewrite <- beq_nat_refl; simpl; auto].
intro e;
case (beq_nat (Zabs_nat i) 0).
exact Hwf.
apply WF_replace1; exact Hwf.
Qed.

Definition replace (v : list) (i : Z) (e : X.element_t) : list :=
Build_list (replace_lst v i e) (WF_replace v i e).

Lemma replace1_length :
forall v : Rlist, forall e : X.element_t, forall n : nat,
List.length v = List.length (replace1 v e n).
induction v; simpl; [reflexivity|].
intros e n; case n; [reflexivity|].
clear n; intros n; rewrite (IHv e n); reflexivity.
Qed.

Lemma replace_length :
forall v : list, forall e : X.element_t, forall i : Z,
Zge (Z_of_nat (length v)) i /\ Zgt i 0 ->
length v = length (replace v i e).
intros [v Hwf] e i; unfold replace; unfold length; simpl; intro Hin;
unfold replace_lst; rewrite (is_valid_bool_true _ _ Hin).
destruct Hin as [_ Hpi]; generalize Hpi;
rewrite <- (Zabs_eq _ (Zlt_le_weak _ _ (Zgt_lt _ _ Hpi)));
rewrite <- inj_Zabs_nat; rewrite Zabs_nat_Z_of_nat.
rewrite <- inj_0; clear; intros Hpi; apply inj_gt_rev in Hpi.
case_eq (beq_nat (Zabs_nat i) 0); [intro Heq; contradict Hpi;
apply beq_nat_true in Heq; rewrite Heq; apply gt_irrefl|intros _].
apply replace1_length; exact Hli.
Qed.

Lemma replace1_element_replaced :
forall v : Rlist, forall e : X.element_t, forall n : nat,
List.length v > n ->
snd(nth n (replace1 v e n) (O,X.e_nl)) = e.
intros v e; induction v; simpl.
intros n Hko; contradict Hko; apply le_not_gt; apply le_O_n.
intros n; case n; simpl; [reflexivity|clear n; intro n].
intro H; apply gt_S_n in H; apply (IHv n H).
Qed.

Lemma replace_element_replaced :
forall v : list, forall e : X.element_t, forall i : Z,
Zge (Z_of_nat (length v)) i /\ Zgt i 0 ->
element (replace v i e) i = e.
intros [v Hwf] e i; unfold replace; unfold length; simpl; intro Hin; 
unfold replace_lst; unfold element; rewrite (is_valid_bool_true _ _ Hin).
destruct Hin as [Hli Hpi]; generalize Hpi Hli;
rewrite <- (Zabs_eq _ (Zlt_le_weak _ _ (Zgt_lt _ _ Hpi)));
rewrite <- inj_Zabs_nat; rewrite Zabs_nat_Z_of_nat.
rewrite <- inj_0; clear Hpi Hli; intros Hpi Hli; apply inj_gt_rev in Hpi;
apply Zge_le in Hli; apply inj_le_rev in Hli.
case_eq (beq_nat (Zabs_nat i) 0); [intro Heq; contradict Hpi;
apply beq_nat_true in Heq; rewrite Heq; apply gt_irrefl|intros Hdiff].
rewrite (is_valid_bool_true _ _); [|split; [apply Zle_ge; apply inj_le;
rewrite (replace1_length v e (pred (Zabs_nat i))) in Hli;
exact Hli|rewrite <- inj_0; apply inj_gt; exact Hpi]].
rewrite Hdiff; rewrite (S_pred _ _ Hpi) in Hli; apply le_S_gt in Hli.
apply (replace1_element_replaced _ _ _ Hli).
Qed.

Lemma replace1_element_diff :
forall v : Rlist, forall e : X.element_t, forall n m : nat,
n <> m ->
snd(nth m (replace1 v e n) (O,X.e_nl)) = snd(nth m v (O,X.e_nl)).
intros v e; induction v; simpl.
intros n m; reflexivity.
intros n m; case n; case m; simpl; [intro Hko; contradict Hko; reflexivity|
reflexivity|reflexivity| clear n m; intros m n].
intro H; apply IHv; intro Heq; apply H; rewrite Heq; reflexivity.
Qed.

Lemma replace_element_diff :
forall v : list, forall e : X.element_t, forall i j : Z,
Zge (Z_of_nat (length v)) i /\ Zgt i 0 ->
Zge (Z_of_nat (length v)) j /\ Zgt j 0 ->
i <> j -> element (replace v i e) j = element v j.
intros [v Hwf] e i j; unfold replace; unfold length; simpl;
intros Hin Hjn; unfold replace_lst; unfold element;
rewrite (is_valid_bool_true _ _ Hin); rewrite (is_valid_bool_true _ _ Hjn).
destruct Hin as [Hli Hpi]; generalize Hpi Hli;
rewrite <- (Zabs_eq _ (Zlt_le_weak _ _ (Zgt_lt _ _ Hpi)));
rewrite <- inj_Zabs_nat; rewrite Zabs_nat_Z_of_nat.
clear Hpi Hli; intros Hpi Hli; rewrite <- inj_0 in Hpi;
apply inj_gt_rev in Hpi; apply Zge_le in Hli; apply inj_le_rev in Hli.
case_eq (beq_nat (Zabs_nat i) 0); [intro Heq; contradict Hpi;
apply beq_nat_true in Heq; rewrite Heq; apply gt_irrefl|intros _].
rewrite (replace1_length v e (pred (Zabs_nat i))) in Hjn;
rewrite (is_valid_bool_true _ _ Hjn);
rewrite <- (replace1_length) in Hjn.
destruct Hjn as [Hlj Hpj]; generalize Hpj Hlj;
rewrite <- (Zabs_eq _ (Zlt_le_weak _ _ (Zgt_lt _ _ Hpj)));
rewrite <- inj_Zabs_nat; rewrite Zabs_nat_Z_of_nat.
clear Hpj Hlj; intros Hpj Hlj Hij; rewrite <- inj_0 in Hpj;
apply inj_gt_rev in Hpj; apply Zge_le in Hlj; apply inj_le_rev in Hlj.
assert (pred (Zabs_nat i) <> pred(Zabs_nat j)); [intro Heq; contradict Hij;
rewrite (S_pred _ _ Hpi); rewrite (S_pred _ _ Hpj);
rewrite Heq; reflexivity|clear Hij].
case_eq (beq_nat (Zabs_nat j) 0); [intro Heq; contradict Hpj;
apply beq_nat_true in Heq; rewrite Heq; apply gt_irrefl|intros _].
apply (replace1_element_diff v e _ _ H).
Qed.

Lemma replace1_to_index :
forall v : Rlist, forall cu : cursor, forall i n : nat,
forall e : X.element_t,
to_index1 v cu n = to_index1 (replace1 v e i) cu n.
intros v cu; induction v; simpl.
reflexivity.
intros i n e; case i; clear i; simpl; [|intro i].
reflexivity.
case (beq_nat cu (fst a)); [reflexivity| apply IHv].
Qed.

Lemma replace_to_index :
forall v : list, forall i : Z, forall e : X.element_t, forall cu : cursor,
to_index v cu = to_index (replace v i e) cu.
intros [v Hwf] i e; unfold replace; unfold length; simpl;
unfold replace_lst; unfold to_index.
case ((Zgt_bool i 0 && Zge_bool (Z_of_nat (List.length v)) i)%bool);
[|rewrite <- beq_nat_refl; reflexivity].
case (beq_nat (Zabs_nat i) 0); [reflexivity|].
intro cu; apply inj_eq; apply replace1_to_index.
Qed.


(*** MAX ***)

Module Type CompareType.

Parameter Inline compare : X.element_t -> X.element_t -> Z.

Axiom compare_refl :
forall e : X.element_t, (compare e e = 0)%Z.

Axiom compare_asym :
forall e1 : X.element_t, forall e2 : X.element_t,
(0 <= compare e1 e2 <-> compare e2 e1 <= 0)%Z.

Axiom compare_trans :
forall e1 : X.element_t, forall e2 : X.element_t, forall e3 : X.element_t,
(compare e1 e2 <= 0)%Z -> (compare e2 e3 <= 0)%Z ->
(compare e1 e3 <= 0)%Z.

End CompareType.

Module Max (C : CompareType).

Fixpoint max2 (l : Rlist) (e : X.element_t) (cu res : nat) : nat :=
match l with
nil => res
| a :: ls => if (Zle_bool (C.compare e (snd a)) (0%Z)) then
max2 ls (snd a) (S cu) cu else max2 ls e (S cu) res
end.

Definition max (l : Rlist) : Z :=
match l with
nil => 0%Z
| a :: ls => Z_of_nat (S(max2 ls (snd a) 1 0))
end.

Lemma max2_has_element :
forall l : Rlist,
forall e : X.element_t, forall res compt : nat,
List.length l + compt > max2 l e compt res /\
compt <= max2 l e compt res \/ res = max2 l e compt res.
induction l; simpl.
intros _ res compt; right; reflexivity.
intros e res compt; rewrite plus_n_Sm;
case (Zle_bool (C.compare e (snd a)) 0).
left; destruct (IHl (snd a) compt (S compt)) as [[Hl Hp] | Heq];
[split; [exact Hl|]|rewrite <- Heq].
apply le_trans with (S compt); [apply le_n_Sn | exact Hp].
split; [apply le_S_gt; rewrite plus_comm;
rewrite (plus_n_O (S compt)) at 1|apply le_refl].
apply plus_le_compat_l; apply le_O_n.
destruct (IHl e res (S compt)) as [[Hl Hp] | Heq];
[left; split; [exact Hl|]|right; exact Heq].
apply le_trans with (S compt); [apply le_n_Sn | exact Hp].
Qed.

Lemma max_has_element1 :
forall l : Rlist,
List.length l <> 0 ->
Zlt 0 (max l) /\ Zle (max l) (Z_of_nat(List.length l)).
intros l; case l; clear l; unfold max.
intros Hko; contradict Hko; reflexivity.
intros a l _; split; [rewrite <- inj_0; apply Zgt_lt;
apply inj_gt; apply gt_Sn_O|apply inj_le; simpl; apply le_n_S].
destruct (max2_has_element l (snd a) 0 1) as [[Hl _]|Heq].
rewrite <- plus_n_Sm in Hl; rewrite <- plus_n_O in Hl; apply gt_S_le;
exact Hl.
rewrite <- Heq; apply le_O_n.
Qed.

Lemma max_has_element :
forall l : list,
length l <> 0 ->
Zlt 0 (max l) /\ Zle (max l) (Z_of_nat(length l)).
intros [l Hwf]; unfold length; simpl; apply max_has_element1.
Qed.

Lemma max2_base :
forall l : Rlist,forall res compt : nat, forall e : X.element_t,
(C.compare (if beq_nat (max2 l e compt res) res then e else
             snd(nth (max2 l e compt res - compt) l (O,X.e_nl)))
           e >= 0)%Z.
induction l; simpl.
intros res compt e; rewrite <- beq_nat_refl.
rewrite C.compare_refl; apply Zle_ge; apply Zle_refl.
intros res compt e; generalize (Zle_cases (C.compare e (snd a)) 0);
case (Zle_bool (C.compare e (snd a)) 0); simpl.
intro Hcomp; case (beq_nat (max2 l (snd a) (S compt) compt) res).
rewrite C.compare_refl; apply Zle_ge; apply Zle_refl.
destruct (max2_has_element l (snd a) compt (S compt)) as [[Hl Hp] | Heq].
generalize (le_plus_minus _ _ Hp); intro HH; rewrite HH;
rewrite plus_Sn_m; rewrite plus_n_Sm; clear HH.
assert(compt + S (max2 l (snd a) (S compt) compt - S compt) - compt =
S (max2 l (snd a) (S compt) compt - S compt));
[symmetry; apply plus_minus; reflexivity|rewrite H; clear H].
generalize (IHl compt (S compt) (snd a));
case_eq (beq_nat (max2 l (snd a) (S compt) compt) compt).
intro Hko; contradict Hp; apply beq_nat_true in Hko;
rewrite Hko; apply le_Sn_n.
intros _ Htrans; apply Zle_ge.
destruct (C.compare_asym (snd (nth (max2 l (snd a) (S compt) compt -
S compt) l (O,X.e_nl))) e) as [_ Himp]; apply Himp; clear Himp.
destruct (C.compare_asym (snd(nth (max2 l (snd a) (S compt) compt -
S compt) l (O,X.e_nl))) (snd a)) as [Himp _]; apply Zge_le in Htrans;
apply Himp in Htrans; clear Himp.
apply (C.compare_trans _ _ _ Hcomp Htrans).
rewrite <- Heq; rewrite minus_diag. 
destruct (C.compare_asym (snd a) e) as [_ Himp]; apply Zle_ge; apply Himp;
exact Hcomp.
intros Hcomp; case_eq (beq_nat (max2 l e (S compt) res) res).
intros _; rewrite C.compare_refl; apply Zle_ge; apply Zle_refl.
destruct (max2_has_element l e res (S compt)) as [[Hl Hp] | Hko];
[intros Hdiff|intro Hneq; contradict Hneq; rewrite <- Hko;
rewrite <- beq_nat_refl; apply Bool.diff_true_false].
generalize (le_plus_minus _ _ Hp); intro HH; rewrite HH;
rewrite plus_Sn_m; rewrite plus_n_Sm.
assert(compt + S (max2 l e (S compt) res - (S compt)) - compt =
S (max2 l e (S compt) res - (S compt))); [symmetry; apply plus_minus;
reflexivity|rewrite H].
generalize (IHl res (S compt) e); rewrite Hdiff; auto.
Qed.

Lemma max2_ex :
forall l : Rlist,forall n res compt : nat, forall e : X.element_t,
compt > res -> List.length l > n ->
res = max2 l e compt res ->
(C.compare e (snd (nth n l (O,X.e_nl))) >= 0)%Z.
induction l; simpl.
intros n res compt e _ Hko; contradict Hko; apply le_not_gt; apply le_O_n.
intros n res compt e Hcr; generalize (Zle_cases (C.compare e (snd a)) 0);
case (Zle_bool (C.compare e (snd a)) 0); [intros _ _ Hko|].
destruct (max2_has_element l (snd a) compt (S compt)) as [[_ Hp] | Heq].
contradict Hp; rewrite <- Hko; apply gt_not_le;
apply gt_trans with compt; [apply gt_Sn_n|exact Hcr].
contradict Hcr; rewrite Heq; rewrite <- Hko; apply gt_irrefl.
case n; clear n.
intros Hex _ _; apply Zle_ge; apply Zlt_le_weak; apply Zgt_lt;
exact Hex.
intros n _ Hl; apply gt_S_n in Hl;
apply (gt_trans _ _ _ (gt_Sn_n compt)) in Hcr;
apply (IHl n res (S compt) e Hcr Hl). 
Qed.

Lemma max2_sup :
forall l : Rlist,forall n res compt : nat, forall e : X.element_t,
compt > res -> List.length l > n ->
(C.compare (if (beq_nat (max2 l e compt res) res)
            then e
            else snd(nth (max2 l e compt res - compt) l (O,X.e_nl)))
        (snd(nth n l (O,X.e_nl))) >= 0)%Z.
induction l; simpl.
intros n res compt e _ Hko; contradict Hko; apply le_not_gt;
apply le_O_n.
intros n res compt e; generalize (Zle_cases (C.compare e (snd a)) 0);
case (Zle_bool (C.compare e (snd a)) 0); intro Hcomp.
intros Hcr; case_eq (beq_nat (max2 l (snd a) (S compt) compt) res).
intro Hko; apply beq_nat_true in Hko;
destruct (max2_has_element l (snd a) compt (S compt)) as [[Hl Hp] | Heq].
apply le_S_gt in Hp; apply (gt_trans _ _ _ Hp) in Hcr; contradict Hcr;
rewrite Hko; apply gt_irrefl.
contradict Hcr; rewrite Heq; rewrite Hko; apply gt_irrefl.
intros _; case n; clear n.
destruct (max2_has_element l (snd a) compt (S compt)) as [[Hl Hp] | Heq].
intros _; generalize (max2_base l compt (S compt) (snd a)).
case_eq (beq_nat (max2 l (snd a) (S compt) compt) compt);
[intro Hko; apply beq_nat_true in Hko; contradict Hp; rewrite Hko;
apply le_Sn_n|intros _].
intro Hex; generalize (le_plus_minus _ _ Hp); intro HH; rewrite HH;
rewrite plus_Sn_m; rewrite plus_n_Sm; clear HH.
assert(compt + S (max2 l (snd a) (S compt) compt - S compt) - compt =
S (max2 l (snd a) (S compt) compt - S compt)); [symmetry;
apply plus_minus;reflexivity|rewrite H; clear H; exact Hex].
intros _; rewrite <- Heq; rewrite minus_diag;
rewrite C.compare_refl; apply Zle_ge; apply Zle_refl.
intros n Hln; apply gt_S_n in Hln.
destruct (max2_has_element l (snd a) compt (S compt)) as [[Hl Hp] | Heq].
generalize (IHl n compt (S compt) (snd a) (gt_Sn_n compt) Hln).
case_eq (beq_nat (max2 l (snd a) (S compt) compt) compt);
[intro Hko; apply beq_nat_true in Hko; contradict Hp; rewrite Hko;
apply le_Sn_n|intros _].
intro Hex; generalize (le_plus_minus _ _ Hp); intro HH; rewrite HH;
rewrite plus_Sn_m; rewrite plus_n_Sm; clear HH.
assert(compt + S (max2 l (snd a) (S compt) compt - S compt) - compt =
S (max2 l (snd a) (S compt) compt - S compt)); [symmetry;
apply plus_minus;reflexivity|rewrite H; clear H; exact Hex].
rewrite <- Heq; rewrite minus_diag.
apply (max2_ex l n _ _ (snd a) (gt_Sn_n compt) Hln Heq).
intros Hcr; case n; clear n; [intros _|].
destruct (max2_has_element l e res (S compt)) as [[Hl Hp] | Heq].
apply (gt_trans _ _ _ (gt_Sn_n _)) in Hcr.
generalize (max2_base l res (S compt) e).
case_eq (beq_nat (max2 l e (S compt) res) res);
[intro Hko; apply beq_nat_true in Hko; contradict Hp; rewrite Hko;
apply gt_not_le; apply Hcr|intros _ Htrans].
apply Zgt_lt in Hcomp; apply Zlt_le_weak in Hcomp.
generalize (le_plus_minus _ _ Hp); intro HH; rewrite HH;
rewrite plus_Sn_m; rewrite plus_n_Sm; clear HH.
assert(compt + S (max2 l e (S compt) res - S compt) - compt =
S (max2 l e (S compt) res - S compt)); [symmetry; apply plus_minus;
reflexivity|rewrite H; clear H; apply Zle_ge].
destruct (C.compare_asym (snd(nth (max2 l e (S compt) res - S compt) l
(O,X.e_nl))) (snd a)) as [_ Himp]; apply Himp; clear Himp.
destruct (C.compare_asym (snd (nth (max2 l e (S compt) res - S compt) l
(O,X.e_nl))) e) as [Himp _];
apply Zge_le in Htrans; apply Himp in Htrans; clear Himp.
destruct (C.compare_asym e (snd a)) as [Himp _]; apply Himp in Hcomp;
clear Himp.
apply (C.compare_trans _ _ _ Hcomp Htrans).
rewrite <- Heq; rewrite <- beq_nat_refl; apply Zle_ge;
apply Zlt_le_weak; apply Zgt_lt; exact Hcomp.
intros n Hln; apply gt_S_n in Hln;
apply (gt_trans _ _ _ (gt_Sn_n _)) in Hcr.
generalize (IHl n res (S compt) e Hcr Hln).
case_eq (beq_nat (max2 l e (S compt) res) res); [auto|intros Hdiff Hex].
destruct (max2_has_element l e res (S compt)) as [[Hl Hp] | Hko];
[|contradict Hdiff; rewrite <- Hko; rewrite <- beq_nat_refl;
apply Bool.diff_true_false].
generalize (le_plus_minus _ _ Hp); intro HH; rewrite HH;
rewrite plus_Sn_m; rewrite plus_n_Sm; clear HH.
assert(compt + S (max2 l e (S compt) res - S compt) - compt =
S (max2 l e (S compt) res - S compt)); [symmetry; apply plus_minus;
reflexivity|rewrite H; clear H; exact Hex].
Qed.

Lemma max2_element :
forall l : Rlist, forall n : nat, forall cu : cursor,
forall e : X.element_t,
n <= List.length l ->
(C.compare (snd(nth (max2 l e 1 0) ((cu,e) :: l) (O,X.e_nl)))
   (snd(nth n ((cu,e) :: l) (O,X.e_nl))) >= 0)%Z.
simpl; intros l n cu e; case n; simpl.
intros _; generalize (max2_base l 0 1 e).
case (max2 l e 1 0).
rewrite <- beq_nat_refl; auto.
clear; intro n; case_eq (beq_nat (S n) 0); [intro Hko;
apply beq_nat_true in Hko; symmetry in Hko; contradict Hko; apply O_S|].
intros _; rewrite <- pred_of_minus; rewrite <- pred_Sn; auto.
clear; intros n H; apply le_S_gt in H.
generalize (max2_sup l n 0 1 e (gt_Sn_O O) H).
case (max2 l e 1 0).
rewrite <- beq_nat_refl; auto.
clear; intro m; case_eq (beq_nat (S m) 0); [intro Hko;
apply beq_nat_true in Hko; symmetry in Hko; contradict Hko; apply O_S|].
intros _; rewrite <- pred_of_minus; rewrite <- pred_Sn; auto.
Qed.

Lemma max_element :
forall v : list, forall i : Z,
Zlt 0 i /\ Zle i (Z_of_nat (length v)) ->
Zge (C.compare (element v (max v)) (element v i)) 0.
intros [v Hwf] i; unfold length; simpl; case v; clear v Hwf.
simpl; intros [Hko Hex]; apply Zlt_gt in Hko; contradict Hko;
apply Zle_not_gt; exact Hex.
unfold element; unfold to_cursor.
intros e l [Hpi Hli]; rewrite (is_valid_bool_true _ i);
[|split; [apply Zle_ge; exact Hli|apply Zlt_gt; exact Hpi]].
destruct (max_has_element1 (e :: l)) as [Hpm Hlm];
[intro Heq; contradict Hli; rewrite Heq; simpl; apply Zlt_not_le;
exact Hpi|].
rewrite (is_valid_bool_true);
[|split; [apply Zle_ge; exact Hlm|apply Zlt_gt; exact Hpm]].
generalize Hpi Hli Hpm Hlm;
rewrite <- (Zabs_eq _ (Zlt_le_weak _ _ Hpi));
unfold max;
repeat(rewrite <- inj_Zabs_nat); repeat(rewrite Zabs_nat_Z_of_nat).
rewrite <- inj_0; clear; intros Hpi Hli Hpm Hlm; apply Zlt_gt in Hpi;
apply Zlt_gt in Hpm; apply inj_gt_rev in Hpi; apply inj_gt_rev in Hpm;
apply inj_le_rev in Hli; apply inj_le_rev in Hlm.
case_eq (beq_nat (Zabs_nat i) 0); [intro Heq; contradict Hpi;
apply beq_nat_true in Heq; rewrite Heq; apply gt_irrefl|intros _].
rewrite <- pred_Sn.
case_eq (beq_nat (S(max2 l (snd e) 1 0)) 0); [intro Heq; contradict Hpm;
apply beq_nat_true in Heq; rewrite Heq; apply gt_irrefl|intros _].
simpl in Hli; simpl in Hlm;
rewrite (S_pred _ _ Hpi) in Hli; apply le_S_n in Hlm; apply le_S_n in Hli.
rewrite (surjective_pairing e); apply (max2_element _ _ _ _ Hli).
Qed.

End Max.

(*** SUM_OF ***)

Module Type WeightType.

Parameter Inline weight : X.element_t -> nat.

End WeightType.

Module Sum_Of (W : WeightType).

Fixpoint sum_of_weight (l : Rlist) : nat :=
match l with
nil => 0
| a :: ls => (W.weight (snd a)) + (sum_of_weight ls) 
end.

Lemma sum_of_nth :
forall v1 v2 : Rlist, List.length v1 = List.length v2 ->
(forall m : nat, List.length v1 > m ->
snd (nth m v1 (0,X.e_nl)) = snd(nth m v2 (O,X.e_nl))) ->
sum_of_weight(v1) = sum_of_weight(v2).
induction v1; simpl.
intro v2; case v2; [reflexivity|intros e l Hko; contradict Hko; apply O_S].
intro v2; case v2; [intros Hko; symmetry in Hko; contradict Hko;
apply O_S|clear v2; intros e v2; simpl].
intros Hl; apply eq_add_S in Hl; intros Hm; rewrite (IHv1 _ Hl);
[generalize (Hm O (gt_Sn_O _)); intro Heq; rewrite Heq; reflexivity|].
intros m Hlm; apply gt_n_S in Hlm; apply (Hm (S m) Hlm).
Qed.

Lemma sum_of_delete1 :
forall v1 v2 : Rlist, forall n : nat,
List.length v1 > n ->
(forall m : nat,
(List.length v2 > m /\ n <= m ->
snd(nth (S m) v1 (O,X.e_nl)) = snd(nth m v2 (O,X.e_nl))) /\
(n > m -> snd(nth m v2 (O,X.e_nl)) = snd(nth m v1 (O,X.e_nl)))) ->
S (List.length v2) = List.length v1 ->
sum_of_weight v1 =
W.weight (snd(nth n v1 (O,X.e_nl))) + sum_of_weight v2.
induction v1; simpl.
intros v2 n Hko; contradict Hko; apply le_not_gt; apply le_O_n.
intros v2 n; case n; clear n.
intros _ Hm Hl; apply eq_add_S in Hl; rewrite (sum_of_nth _ _ Hl);
[reflexivity|].
intros m Hlm; destruct (Hm m) as [Hex _]; clear Hm; symmetry;
apply (Hex (conj Hlm (le_O_n m))).
case v2; clear v2; simpl.
case v1; [intros n Hko; apply gt_S_n in Hko; contradict Hko;
apply le_not_gt; apply le_O_n|intros aa ll n _ _ Hko;
apply eq_add_S in Hko; contradict Hko; apply O_S].
intros a2 v2 n Hln Hm Hlg;
apply gt_S_n in Hln; apply eq_add_S in Hlg.
destruct (Hm O) as [_ Heq]; rewrite (Heq (gt_Sn_O n)); clear Heq.
rewrite plus_assoc; rewrite (plus_comm _ (W.weight (snd a)));
rewrite <- plus_assoc; rewrite (IHv1 v2 n Hln); [reflexivity| |exact Hlg].
intros m; destruct (Hm (S m)) as [Hm1 Hm2]; clear Hm; split;
[intros [Hlm Hnm]; apply Hm1|intro Hnm; apply Hm2].
split; [apply gt_n_S; exact Hlm|apply le_n_S; exact Hnm].
apply gt_n_S; exact Hnm.
Qed.

Lemma sum_of_delete :
forall v1 v2 : list, forall i : Z,
Zge (Z_of_nat (length v1)) i /\ Zgt i 0 ->
(forall j : Z,
(Zgt (Z_of_nat (length v1)) j /\ Zge j i ->
element v1 (j + (Z_of_nat 1)) = element v2 j) /\
(Zlt 0 j /\ Zlt j i -> element v2 j = element v1 j)) ->
S (length v2) = length v1 ->
sum_of_weight v1 =
W.weight (element v1 i) + sum_of_weight v2.
unfold element; intros [v1 H1] [v2 H2]; unfold length;
simpl; clear H1 H2; assert ((1=Z_of_nat(1))%Z); [auto|rewrite H].
intros i Hin; rewrite (is_valid_bool_true _ _ Hin).
destruct Hin as [Hli Hpi]; generalize Hli Hpi.
rewrite <- (Zabs_eq _ (Zlt_le_weak _ _ (Zgt_lt _ _ Hpi)));
rewrite <- inj_Zabs_nat; rewrite Zabs_nat_Z_of_nat.
rewrite <- inj_0; clear; intros Hli Hpi; apply inj_gt_rev in Hpi;
apply Zge_le in Hli; apply inj_le_rev in Hli.
case_eq (beq_nat (Zabs_nat i) 0); [intro Heq; contradict Hpi;
apply beq_nat_true in Heq; rewrite Heq; apply gt_irrefl|intros _].
intros Hcomp Hlgth; apply sum_of_delete1; [apply gt_S_n;
rewrite <- (S_pred _ _ Hpi); apply le_gt_S; exact Hli| | exact Hlgth].
intros m; split; intro Hm; generalize (Hcomp (Z_of_nat (S m)));
clear Hcomp; rewrite Zabs_nat_Z_of_nat; rewrite <- inj_plus;
rewrite <- plus_n_Sm; rewrite <- plus_n_O;
[intros [Hcomp _]|intros [_ Hcomp]].
destruct Hm as [Hlm Him]; apply gt_n_S in Hlm; rewrite Hlgth in Hlm;
apply inj_gt in Hlm; apply le_n_S in Him; apply inj_le in Him;
rewrite <- (S_pred _ _ Hpi) in Him;
generalize (Hcomp (conj Hlm (Zle_ge _ _ Him))); clear Hcomp; rewrite inj_0.
apply Zgt_le_succ in Hlm; rewrite <- inj_S in Hlm;
apply inj_gt in Hpi; rewrite inj_0 in Hpi.
rewrite (is_valid_bool_true _ _ (conj (Zle_ge _ _ Hlm)
(Zle_gt_trans _ _ _ Him Hpi))).
rewrite <- Hlgth in Hlm; repeat (rewrite inj_S in Hlm);
apply Zsucc_le_reg in Hlm; rewrite <- inj_S in Hlm.
rewrite (is_valid_bool_true _ _ (conj (Zle_ge _ _ Hlm)
(Zle_gt_trans _ _ _ Him Hpi))).
rewrite Zabs_nat_Z_of_nat; case_eq (beq_nat (S (S m)) 0);
[intro Hko; apply beq_nat_true in Hko; symmetry in Hko; contradict Hko;
apply O_S|intros _]; case_eq (beq_nat (S m) 0);
[intro Hko; apply beq_nat_true in Hko; symmetry in Hko; contradict Hko;
apply O_S|intros _].
rewrite pred_Sn with m; auto.
generalize (gt_Sn_O m); intro Hmp; apply gt_n_S in Hm;
rewrite <- (S_pred _ _ Hpi) in Hm; apply inj_gt in Hm; apply inj_gt in Hmp;
rewrite inj_0 in Hmp; generalize (Hcomp (conj (Zgt_lt _ _ Hmp)
(Zgt_lt _ _ Hm))); clear Hcomp; rewrite inj_0.
apply inj_le in Hli.
rewrite (is_valid_bool_true _ _ (conj (Zle_ge _ _ (Zle_trans _ _ _
(Zlt_le_weak _ _ (Zgt_lt _ _ Hm)) Hli)) Hmp)).
rewrite <- Hlgth in Hli; rewrite inj_S in Hli; apply Zgt_le_succ in Hm.
rewrite (is_valid_bool_true _ _ (conj (Zle_ge _ _(Zsucc_le_reg _ _ 
(Zle_trans _ _ _ Hm Hli))) Hmp)).
case_eq (beq_nat (S m) 0);
[intro Hko; apply beq_nat_true in Hko; symmetry in Hko; contradict Hko;
apply O_S|intros _]; rewrite <- pred_Sn; auto.
Qed.

Lemma sum_of_replace1 :
forall v1 v2 : Rlist, forall n : nat,
List.length v2 = List.length v1 -> List.length v1 > n ->
(forall m : nat, List.length v1 > m /\ n <> m ->
snd(nth m v2 (O,X.e_nl)) = snd(nth m v1 (O,X.e_nl))) ->
sum_of_weight v1 + W.weight (snd(nth n v2 (O,X.e_nl))) =
W.weight (snd(nth n v1 (O,X.e_nl))) + sum_of_weight v2.
induction v1; simpl.
intros v2 n _ Hko; contradict Hko; apply le_not_gt; apply le_O_n.
intros v2 n; case n; simpl; clear n; [|intros n].
case v2; simpl; clear v2; [intro Hko; contradict Hko; apply O_S|].
intros a2 v2 Hl _ Hcomp; apply eq_add_S in Hl;
rewrite (plus_comm (W.weight (snd a2))); rewrite plus_assoc.
rewrite (sum_of_nth v2 v1 Hl); [reflexivity|].
rewrite Hl; intros m Hlm;
apply (Hcomp (S m) (conj (gt_n_S _ _ Hlm) (O_S m))).
case v2; simpl; clear v2; [intro Hko; contradict Hko; apply O_S|].
intros a2 v2 Hl Hln Hcomp; apply eq_add_S in Hl; apply gt_S_n in Hln;
rewrite (Hcomp O); [|split; [apply gt_Sn_O| intro Heq; symmetry in Heq;
contradict Heq; apply O_S]].
rewrite plus_assoc; rewrite (plus_comm _ (W.weight (snd a)));
repeat (rewrite <- plus_assoc); rewrite (IHv1 v2 n Hl Hln); [reflexivity|].
intros m [Hlm Hdiff]; apply (Hcomp (S m)); split;
[apply gt_n_S; exact Hlm | intro HH; apply Hdiff; apply eq_add_S; exact HH].
Qed.

Lemma sum_of_replace :
forall v1 v2 : list, forall i : Z, forall e : X.element_t,
length v2 = length v1 ->
Zge (Z_of_nat (length v1)) i /\ Zgt i 0 ->
element v2 i = e ->
(forall j : Z, Zge (Z_of_nat (length v1)) j /\ Zgt j 0 -> i <> j ->
element v2 j = element v1 j) ->
sum_of_weight v1 + W.weight e =
W.weight (element v1 i) + sum_of_weight v2.
unfold element; intros [v1 H1] [v2 H2]; unfold length;
simpl; clear H1 H2.
intros i e Hlgth Hin; rewrite Hlgth;
rewrite (is_valid_bool_true _ _ Hin).
destruct Hin as [Hli Hpi]; generalize Hli Hpi.
rewrite <- (Zabs_eq _ (Zlt_le_weak _ _ (Zgt_lt _ _ Hpi)));
rewrite <- inj_Zabs_nat; rewrite Zabs_nat_Z_of_nat.
rewrite <- inj_0; clear Hli Hpi; intros Hli Hpi; apply inj_gt_rev in Hpi;
apply Zge_le in Hli; apply inj_le_rev in Hli.
case_eq (beq_nat (Zabs_nat i) 0); [intro Heq; contradict Hpi;
apply beq_nat_true in Heq; rewrite Heq; apply gt_irrefl|intros _].
intros Hel Hcomp; rewrite <- Hel.
rewrite (S_pred _ _ Hpi) in Hli.
apply (sum_of_replace1 v1 v2 _ Hlgth (le_S_gt _ _ Hli)).
intros m [Hlm Hdiff]; generalize (gt_Sn_O m); intros Hpm.
apply inj_gt in Hpm; apply gt_le_S in Hlm; apply inj_le in Hlm;
generalize (Hcomp (Z_of_nat (S m)) (conj (Zle_ge _ _ Hlm) Hpm)).
rewrite inj_0; rewrite (is_valid_bool_true _ _ (conj (Zle_ge _ _ Hlm) Hpm)).
rewrite Zabs_nat_Z_of_nat; case_eq (beq_nat (S m) 0);
[intro Hko; apply beq_nat_true in Hko; symmetry in Hko;
 contradict Hko; apply O_S |intros _].
rewrite <- (pred_Sn m); intro HH; apply HH.
intros Heq; apply Hdiff; apply inj_eq_rev in Heq; apply eq_add_S;
rewrite <- (S_pred _ _ Hpi); exact Heq.
Qed.

Lemma sum_of_empty :
forall l : list, length l = 0 -> sum_of_weight l = 0.
intros [l Hwf]; unfold length; simpl; 
induction l; simpl.
reflexivity.
intro Hko; symmetry in Hko; contradict Hko; apply O_S.
Qed.

Lemma sum_of_equal :
forall v1 v2 : list, length v1 = length v2 ->
(forall i : Z, Zge (Z_of_nat (length v1)) i /\ Zgt i 0 ->
element v1 i = element v2 i) ->
sum_of_weight(v1) = sum_of_weight(v2).
unfold element; intros [v1 H1] [v2 H2]; unfold length;
simpl; clear H1 H2.
intros Hl Hcomp; rewrite <- Hl in Hcomp; apply (sum_of_nth v1 v2 Hl).
intros m Hlm; generalize (gt_Sn_O m); intro Hpm;
apply inj_gt in Hpm; apply gt_le_S in Hlm; apply inj_le in Hlm.
generalize (Hcomp (Z_of_nat (S m)) (conj (Zle_ge _ _ Hlm) Hpm)).
rewrite (is_valid_bool_true _ _ (conj (Zle_ge _ _ Hlm) Hpm)).
rewrite Zabs_nat_Z_of_nat; case_eq (beq_nat (S m) 0);
[intro Hko; apply beq_nat_true in Hko; symmetry in Hko;
 contradict Hko; apply O_S |intros _].
rewrite <- pred_Sn; auto.
Qed.

Lemma sum_of_left1 :
forall v : Rlist, forall n : nat,
List.length v > n ->
sum_of_weight (firstn (S n) v) =
sum_of_weight (firstn n v) + W.weight (snd(nth n v (O,X.e_nl))).
induction v; simpl; intros n.
intro Hko; contradict Hko; apply le_not_gt; apply le_O_n.
case n; clear n; [|intro n].
simpl; intros _; rewrite <- plus_n_O; reflexivity.
simpl sum_of_weight at 2.
intros Hl; apply gt_S_n in Hl; rewrite (IHv n Hl);
rewrite plus_assoc; reflexivity.
Qed.

Lemma firstn_length :
forall v : Rlist,
firstn (List.length v) v = v.
induction v; simpl.
reflexivity.
rewrite IHv; reflexivity.
Qed.

Lemma sum_of_left :
forall v : list, forall i : Z,
Zge (Z_of_nat (length v) + 1) i /\ Zgt i 1 ->
sum_of_weight (left v i) =
sum_of_weight (left v (i - 1)) + W.weight (element v (i - 1)).
unfold element; intros [v H]; unfold length; simpl; clear H.
intros i [Hil Hip]; unfold left; unfold left1; unfold element.
rewrite <- (Zplus_minus 1 i) in Hil; rewrite Zplus_comm in Hil.
apply Zge_le in Hil; apply Zplus_le_reg_l in Hil; apply Zle_ge in Hil.
rewrite <- (Zplus_0_r 1) in Hip; rewrite <- (Zplus_minus 1 i) in Hip;
apply Zgt_lt in Hip; apply Zplus_lt_reg_l in Hip; apply Zlt_gt in Hip.
rewrite (is_valid_bool_true _ _ (conj Hil Hip)).
rewrite <- (Zplus_minus 1 i); rewrite Zminus_plus.
generalize Hil Hip;
rewrite <- (Zabs_eq _ (Zlt_le_weak _ _ (Zgt_lt _ _ Hip)));
rewrite <- inj_Zabs_nat; rewrite Zabs_nat_Z_of_nat.
clear; generalize (Zabs_nat (i - 1)); intros n Hnl Hnp.
assert (1%Z = Z_of_nat 1); [auto|rewrite H; clear H].
rewrite <- inj_plus; simpl plus; rewrite <- inj_0 in Hnp;
apply inj_gt_rev in Hnp; apply Zge_le in Hnl; apply inj_le_rev in Hnl.
case_eq (beq_nat n 0); [intro Heq; contradict Hnp;
apply beq_nat_true in Heq; rewrite Heq; apply gt_irrefl|intros _].
generalize (bool_is_valid v (Z_of_nat (S n)));
case ((Zgt_bool (Z_of_nat (S n)) 0
&& Zge_bool (Z_of_nat (List.length v)) (Z_of_nat (S n)))%bool);
rewrite <- inj_0; [rewrite Zabs_nat_Z_of_nat|rewrite <- beq_nat_refl].
intros [Hln _]; apply Zge_le in Hln; apply inj_le_rev in Hln;
clear Hnl; case_eq (beq_nat (S n) 0);
[intro Hko; apply beq_nat_true in Hko; symmetry in Hko;
 contradict Hko; apply O_S |intros _].
rewrite <- pred_Sn; rewrite (S_pred _ _ Hnp) at 1.
apply sum_of_left1.
apply (gt_trans _ _ _ (le_S_gt _ _ Hln) (le_S_gt _ _ (lt_pred_n_n _
(gt_le_S _ _ Hnp)))).
intros [Hko|Hln]; [apply inj_le_rev in Hko; contradict Hko; apply le_Sn_O|].
rewrite <- (firstn_length v) at 1;
apply inj_gt_rev in Hln; apply gt_S_le in Hln;
rewrite (le_antisym _ _ Hln Hnl).
rewrite (S_pred _ _ Hnp) at 1; apply sum_of_left1.
rewrite (le_antisym _ _ Hln Hnl).
apply le_S_gt; apply lt_pred_n_n; apply gt_le_S; exact Hnp.
Qed.

Lemma sum_of_right1 :
forall v : Rlist, forall n : nat,
List.length v > n ->
sum_of_weight (skipn n v) =
W.weight (snd(nth n v (O,X.e_nl))) +
sum_of_weight (skipn (S n) v).
induction v; simpl; intros n.
intro Hko; contradict Hko; apply le_not_gt; apply le_O_n.
case n; clear n; [|intro n].
simpl; intros _; reflexivity.
simpl sum_of_weight at 1.
intros Hl; apply gt_S_n in Hl; rewrite (IHv n Hl); reflexivity.
Qed.

Lemma skipn_length :
forall v : Rlist,
skipn (List.length v) v = nil.
induction v; simpl.
reflexivity.
rewrite IHv; reflexivity.
Qed.

Lemma sum_of_invalidate :
forall l : Rlist, forall n : nat,
sum_of_weight(Shift.invalidate l n)=sum_of_weight l.
intros l n; apply sum_of_nth.
apply Shift.invalidate_length.
intros m H; apply Shift.invalidate_element.
Qed.

Lemma sum_of_right :
forall v : list, forall i : Z,
Zge (Z_of_nat (length v) + 1) i /\ Zgt i 1 ->
sum_of_weight (right v (i - 1)) =
W.weight (element v (i - 1)) +
sum_of_weight (Raw_Vector.right v i).
unfold element; intros [v H]; unfold length; simpl; clear H.
unfold right; unfold element; unfold right1; intros i [Hil Hip].
rewrite <- (Zplus_minus 1 i) in Hil; rewrite Zplus_comm in Hil.
apply Zge_le in Hil; apply Zplus_le_reg_l in Hil; apply Zle_ge in Hil.
rewrite <- (Zplus_0_r 1) in Hip; rewrite <- (Zplus_minus 1 i) in Hip;
apply Zgt_lt in Hip; apply Zplus_lt_reg_l in Hip; apply Zlt_gt in Hip.
rewrite (is_valid_bool_true _ _ (conj Hil Hip)).
rewrite <- (Zplus_minus 1 i); rewrite Zminus_plus.
generalize Hil Hip;
rewrite <- (Zabs_eq _ (Zlt_le_weak _ _ (Zgt_lt _ _ Hip)));
rewrite <- inj_Zabs_nat; rewrite Zabs_nat_Z_of_nat.
clear; generalize (Zabs_nat (i - 1)); intros n Hnl Hnp.
assert (1%Z = Z_of_nat 1); [auto|rewrite H; clear H].
rewrite <- inj_plus; rewrite <- inj_0 in Hnp;
apply inj_gt_rev in Hnp; apply Zge_le in Hnl; apply inj_le_rev in Hnl.
case_eq (beq_nat n 0); [intro Heq; contradict Hnp;
apply beq_nat_true in Heq; rewrite Heq; apply gt_irrefl|intros _].
generalize (bool_is_valid v (Z_of_nat (1 + n)));
case ((Zgt_bool (Z_of_nat (1 + n)) 0
&& Zge_bool (Z_of_nat (List.length v)) (Z_of_nat (1 + n)))%bool);
rewrite <- inj_0; [rewrite Zabs_nat_Z_of_nat|rewrite <- beq_nat_refl].
intros [Hln _]; apply Zge_le in Hln; apply inj_le_rev in Hln;
clear Hnl; case_eq (beq_nat (1 + n) 0);
[intro Hko; apply beq_nat_true in Hko; symmetry in Hko;
 contradict Hko; simpl; apply O_S |intros _; simpl in Hln].
simpl plus; rewrite (S_pred _ _ Hnp) at 3.
repeat(rewrite sum_of_invalidate); apply sum_of_right1.
apply (gt_trans _ _ _ (le_S_gt _ _ Hln) (le_S_gt _ _ (lt_pred_n_n _
(gt_le_S _ _ Hnp)))).
intros [Hko|Hln]; [apply inj_le_rev in Hko; contradict Hko; apply le_Sn_O|].
rewrite <- (skipn_length v);
apply inj_gt_rev in Hln; apply gt_S_le in Hln;
rewrite (le_antisym _ _ Hln Hnl).
rewrite sum_of_invalidate; 
rewrite (S_pred _ _ Hnp) at 3; apply sum_of_right1.
rewrite (le_antisym _ _ Hln Hnl).
apply le_S_gt; apply lt_pred_n_n; apply gt_le_S; exact Hnp.
Qed.

End Sum_Of.
End Raw_Vector.