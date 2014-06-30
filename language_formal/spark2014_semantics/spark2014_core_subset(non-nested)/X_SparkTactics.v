(*
Copyright (c) 2012 Robby, Kansas State University.        
All rights reserved. This program and the accompanying materials      
are made available under the terms of the Eclipse Public License v1.0 
which accompanies this distribution, and is available at              
http://www.eclipse.org/legal/epl-v10.html                             
*)

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
