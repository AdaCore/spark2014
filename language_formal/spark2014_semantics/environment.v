Require Export language.
Require Export values.

(*
    stack  /-----------------------------
              |- stack data structure
              | -----------------------------
              |- stack operations
              | -----------------------------
              |- stack lemmas
              | -----------------------------
*)

(* # stack as a list *)
Definition stack : Type := list (idnum * val).

(* # stack operations *)
Function reside (x : idnum) (s : stack) := 
    match s with 
    | (y, v) :: s' =>
      if beq_nat x y then
        true
      else 
        reside x s' 
    | nil => false
    end.

(* fetch the value of x that has already been initialized in stack *)
Function fetch (x : idnum) (s : stack): option value := 
    match s with 
    | (y, v) :: s' =>
      if beq_nat x y then
        match v with
        | Value v => Some v
        | Vundef => None
        end
      else fetch x s' 
    | nil => None
    end.

(* update the latest binding for x *)
Function update (s: stack) (x : idnum) (v: val): option stack := 
    match s with 
    | (y, v') :: s' => 
      if beq_nat x y then 
        Some ((y,v)::s') 
      else 
        match update s' x v with
        | Some s'' => Some ((y,v')::s'')
        | None => None
        end
   | nil => None
   end.

(* # lemmas about stack operations *)
Lemma fetch_in: forall x s v, fetch x s = Some v -> List.In (x, Value v) s.
Proof.
    intros x s.
    functional induction (fetch x s).
  - intros v H.
    inversion H; clear H; subst.
    rewrite beq_nat_true_iff in e0.
    rewrite e0.
    simpl.
    left;auto.
  - intros v H.
    inversion H. 
  - intros v0 H.
    simpl.
    right.
    apply IHo.
    assumption.
  - intros v H.
    inversion H.
Qed.

Lemma update_in: forall s x v' s', Some s' = update s x v' -> (exists v, List.In (x, v) s).
Proof.
    intros s x v'.
    functional induction (update s x v');
    try match goal with
    | [h: beq_nat _ _ = true |- _ ] => rewrite beq_nat_true_iff in h; subst
    end; intros s1 h1.
  - exists v'. 
    simpl. left; auto.
  - symmetry in e1.
    specialize (IHo s'' e1).
    inversion IHo.
    exists x0. simpl. 
    right; assumption.
  - inversion h1.
  - inversion h1.
Qed.
    
Lemma in_update: forall s x v' y v s',
                   Some s' = update s x v' ->
                   List.In (y, v) s'
                   -> ((y=x /\ v=v') \/ List.In (y,v) s).
Proof.
    intros s x v'.
    functional induction (update s x v'); simpl; intros y0 v0 s0 h h'; subst;
    (inversion h; clear h); subst.
    rewrite beq_nat_true_iff in e0; subst.
  - destruct h'.
    + left. inversion H; auto.
    + right. right; assumption.
  - symmetry in e1.
    specialize (IHo y0 v0 s'' e1).
    destruct h'.
    + right. left. assumption.
    + specialize (IHo H). 
       destruct IHo as [h | h'].
       *  left; assumption.
       * right. right; assumption.
Qed.

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)
(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)

(*
    symbol_table  /-----------------------------
                           |- symtb data structure
                           | -----------------------------
                           |- symtb operations
                           | -----------------------------
                           |- symtb lemmas (to be added)
                           | -----------------------------
*)

(* # symbol table: var -> (mode * type) *)
Definition symtb: Type := list (idnum * (mode * typ)).

Fixpoint lookup (x : idnum) (tb: symtb) := 
   match tb with 
   | (y, (m,t)) :: tb' => if (beq_nat x y) then Some (m, t) else lookup x tb' 
   | nil => None
   end.

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)
(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)

(* 
    possible state after running a command:
    - (1) a normal resultant stack
    - (2) undefined variables (in expression or assigned to an undefined variable), 
            uninitialized variables, type checking failure
    - (3) a security constraint is violated (overflow, division by zero)
*)
Inductive state: Type :=
    | SNormal: stack -> state
    | SException: state
    | SUnterminated: state.
(*    | SAbnormal: state (* for state (1) above *) *)



 