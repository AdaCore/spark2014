(*
Copyright (c) 2012 Robby, Kansas State University.        
All rights reserved. This program and the accompanying materials      
are made available under the terms of the Eclipse Public License v1.0 
which accompanies this distribution, and is available at              
http://www.eclipse.org/legal/epl-v10.html                             
*)

Require Export X_Case.
Require Import X_CpdtTactics.

Create HintDb X_Lib.

(* usage:
         Lemma X: A -> B. 
         Hint Resolve X: X_Lib.
*)

Ltac dup H H' := 
  match type of H with
  | ?X => assert (H' : X); trivial
  end.

Ltac smack := try autorewrite with X_Lib in *; crush; eauto.

Tactic Notation "induction" "list" ident(l) :=
  induction l; [ Case "nil" | Case "cons" ].

Tactic Notation "sub" "induction" "list" ident(l) :=
  induction l; [ SCase "nil" | SCase "cons" ].

Tactic Notation "sub" "sub" "induction" "list" ident(l) :=
  induction l; [ SSCase "nil" | SSCase "cons" ].

Tactic Notation "destruct" "list" ident(l) :=
  destruct l; [ Case "nil" | Case "cons" ].

Tactic Notation "sub" "destruct" "list" ident(l) :=
  destruct l; [ SCase "nil" | SCase "cons" ].

Tactic Notation "sub" "sub" "destruct" "list" ident(l) :=
  destruct l; [ SSCase "nil" | SSCase "cons" ].

Tactic Notation "destruct" "option" ident(o) :=
  destruct o; [ Case "None" | Case "Some" ].

Tactic Notation "sub" "destruct" "option" ident(o) :=
  destruct o; [ SCase "None" | SCase "Some" ].

Tactic Notation "sub" "sub" "destruct" "option" ident(o) :=
  destruct o; [ SSCase "None" | SSCase "Some" ].
