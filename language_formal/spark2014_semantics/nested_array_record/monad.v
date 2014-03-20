

Notation "'Let' 'some' x ':=' t 'in' u " :=
  (match t with
       Some x => u
     | None => None
   end)
    (at level 60,right associativity,
    format "'[' 'Let'  'some'  x  ':=' '/ ' '['  t  ']' 'in'  '//' u ']'")
  : option_monad_scope.

Notation "'Let' 'someb' x ':=' t 'in' u " :=
  (match t with
       Some x => u
     | None => false
   end)
    (at level 60,right associativity,
    format "'[' 'Let'  'someb'  x  ':=' '/ ' '['  t  ']' 'in'  '//' u ']'")
  : option_monad_scope.

Notation Return := Some (only parsing).

Module EXAMPLE.
  Open Scope option_monad_scope.
  Definition essai1 := Return 1.

  Definition essai :=
    Let some x := Return 1 in
    Let some y := Return 2 in
    Return (x+y)%nat.

  Eval compute in essai.

End EXAMPLE.

(*
Inductive Result (TypeExc A:Type) : Type :=
  Return: A -> Result TypeExc A
| Raise: TypeExc -> Result TypeExc A.

Arguments Raise {TypeExc} {A} _.
Arguments Return {TypeExc} {A} _.

(* Definition Return {A:Type} : A -> (A + E) := @inl A E. *)


Definition Bind {TypeExc A B:Type} (x:Result TypeExc A) (f:A -> Result TypeExc B): Result TypeExc B :=
  match x with
    | Return x => (f x)
    | Raise e => Raise e
  end.

Definition TryLet {TypeExc TypeExc' A B:Type} (x:Result TypeExc A) (f:A -> Result TypeExc' B)
           (catch:TypeExc -> Result TypeExc' B): Result TypeExc' B :=
  match x with
    | Return x => f x
    | Raise e => catch e
  end.



Notation "'Let' 'val' x ':=' t 'in' u " :=
  (match t with
       Return x => u
     | Raise e => Raise e
   end)
    (at level 60,right associativity,
    format "'[' 'Let'  'val'  x  ':=' '/ ' '['  t  ']' 'in'  '//'  u ']'").

Notation "'try' t 'with' e '=>' u " :=
  (match t with
       Return x => Return x
     | Raise e => u
   end)
    (at level 60,only parsing).


Notation "'Lettry' 'val' t ':=' v 'in' f 'catch' e => catche " :=
  (match v with
    | Return t => f
    | Raise e => catche
  end)
    (at level 60,only parsing).



Definition BindO {A B:Type} (x:option A) (f:A -> option B): option B :=
  match x with
    | Some x => f x
    | None => None
  end.

Notation "'Let' 'some' x ':=' t 'in' u " :=
  (match t with Some x => u | None => None end)
    (at level 60,right associativity,
    format "'[' 'Let'  'some'  x  ':=' '/ ' '['  t  ']' 'in'  '//'  u ']'").



Definition essai1 := @Return unit _ 1.
(*
Definition essai :=
  Let val x := Return 1 in
  Let val y := Return 2 in
  Return (x+y)%nat.

Definition essai3 :=
  try
    Let val x := Return 1 in
    Let val y := Raise tt in
    Return (x+y)%nat
  with e => (Return 42).

Eval compute in essai3.
*)
*)