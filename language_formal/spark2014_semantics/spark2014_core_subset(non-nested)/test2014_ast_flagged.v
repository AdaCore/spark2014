Require Import language_flagged.

Definition p := 
(* Compilation Unit *)
Library_Unit_X 1
  (* Compilation Unit - Unit Declaration *)
  (Library_Subprogram_X 2
    (* Procedure Body Declaration *)
    (Global_Procedure_X 3
      (mkprocedure_declaration_x 4
        (* Procedure Name *)
        ((*Factorial*) 1)
        (* Formal Parameters *)
        (
        (mkparameter_specification_x 5 ((*N*) 1) Integer In) :: 
        (mkparameter_specification_x 6 ((*M*) 2) Integer Out) :: nil) 
        (* Procedure Contract *)
        (nil)  
        (* Object Declarations *)
        ((D_Seq_Declaration_X 7 
      (D_Object_Declaration_X 8 (mkobject_declaration_x 9 ((*Result*) 3) Integer (Some ((E_Literal_X 10 (Integer_Literal 1) (nil)))))) 
      (D_Object_Declaration_X 11 (mkobject_declaration_x 12 ((*T*) 4) Integer None))))
        (* Procedure Body *)
          (S_Sequence_X 13
          (S_Assignment_X 14 (E_Identifier_X 15 ((*T*) 4) (nil)) (E_Name_X 16 (E_Identifier_X 17 ((*N*) 1) (nil)) (nil))) 
          (S_Sequence_X 18
          (S_While_Loop_X 19 (E_Binary_Operation_X 20 Greater_Than (E_Name_X 21 (E_Identifier_X 22 ((*T*) 4) (nil)) (nil)) (E_Literal_X 23 (Integer_Literal 0) (nil)) (nil))
            (S_Sequence_X 24
            (S_Assignment_X 25 (E_Identifier_X 26 ((*Result*) 3) (nil)) (E_Binary_Operation_X 27 Multiply (E_Name_X 28 (E_Identifier_X 29 ((*Result*) 3) (nil)) (nil)) (E_Name_X 30 (E_Identifier_X 31 ((*T*) 4) (nil)) (nil)) (Do_Overflow_Check :: nil))) 
            (S_Assignment_X 32 (E_Identifier_X 33 ((*T*) 4) (nil)) (E_Binary_Operation_X 34 Minus (E_Name_X 35 (E_Identifier_X 36 ((*T*) 4) (nil)) (nil)) (E_Literal_X 37 (Integer_Literal 1) (nil)) (Do_Overflow_Check :: nil))))
          ) 
          (S_Assignment_X 38 (E_Identifier_X 39 ((*M*) 2) (nil)) (E_Name_X 40 (E_Identifier_X 41 ((*Result*) 3) (nil)) (nil)))))
      )
    )
  )
 .
