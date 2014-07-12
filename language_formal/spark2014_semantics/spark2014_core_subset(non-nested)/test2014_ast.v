Require Import language_flagged.

Definition p := 
(* Compilation Unit *)
Library_Unit 1
  (* Compilation Unit - Unit Declaration *)
  (Library_Subprogram 2
    (* Procedure Body Declaration *)
    (Global_Procedure 3
      (mkprocedure_declaration 4
        (* Procedure Name *)
        ((*Factorial*) 1)
        (* Formal Parameters *)
        (
        (mkparameter_specification 5 ((*N*) 1) Integer In) :: 
        (mkparameter_specification 6 ((*M*) 2) Integer Out) :: nil) 
        (* Procedure Contract *)
        (nil)  
        (* Object Declarations *)
        ((D_Seq_Declaration 7 
      (D_Object_Declaration 8 (mkobject_declaration 9 ((*Result*) 3) Integer (Some ((E_Literal 10 (Integer_Literal 1) (**(nil)**)))))) 
      (D_Object_Declaration 11 (mkobject_declaration 12 ((*T*) 4) Integer None))))
        (* Procedure Body *)
          (S_Sequence 13
          (S_Assignment 14 (E_Identifier 15 ((*T*) 4) (**(nil)**)) (E_Name 16 (E_Identifier 17 ((*N*) 1) (**(nil)**)) (**(nil)**))) 
          (S_Sequence 18
          (S_While_Loop 19 (E_Binary_Operation 20 Greater_Than (E_Name 21 (E_Identifier 22 ((*T*) 4) (**(nil)**)) (**(nil)**)) (E_Literal 23 (Integer_Literal 0) (**(nil)**)) (**(nil)**))
            (S_Sequence 24
            (S_Assignment 25 (E_Identifier 26 ((*Result*) 3) (**(nil)**)) (E_Binary_Operation 27 Multiply (E_Name 28 (E_Identifier 29 ((*Result*) 3) (**(nil)**)) (**(nil)**)) (E_Name 30 (E_Identifier 31 ((*T*) 4) (**(nil)**)) (**(nil)**)) (**(Do_Overflow_Check :: nil)**))) 
            (S_Assignment 32 (E_Identifier 33 ((*T*) 4) (**(nil)**)) (E_Binary_Operation 34 Minus (E_Name 35 (E_Identifier 36 ((*T*) 4) (**(nil)**)) (**(nil)**)) (E_Literal 37 (Integer_Literal 1) (**(nil)**)) (**(Do_Overflow_Check :: nil)**))))
          ) 
          (S_Assignment 38 (E_Identifier 39 ((*M*) 2) (**(nil)**)) (E_Name 40 (E_Identifier 41 ((*Result*) 3) (**(nil)**)) (**(nil)**)))))
      )
    )
  )
 .
