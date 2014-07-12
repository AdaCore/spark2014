Require Import language_flagged.

Definition p := 
(* Compilation Unit *)
Library_Unit_XX 1
  (* Compilation Unit - Unit Declaration *)
  (Library_Subprogram_XX 2
    (* Procedure Body Declaration *)
    (Global_Procedure_XX 3
      (mkprocedure_declaration_xx 4
        (* Procedure Name *)
        ((*Factorial*) 1)
        (* Formal Parameters *)
        (
        (mkparameter_specification_xx 5 ((*N*) 1) Integer In) :: 
        (mkparameter_specification_xx 6 ((*M*) 2) Integer Out) :: nil) 
        (* Procedure Contract *)
        (nil)  
        (* Object Declarations *)
        ((D_Seq_Declaration_XX 7 
      (D_Object_Declaration_XX 8 (mkobject_declaration_xx 9 ((*Result*) 3) Integer (Some ((E_Literal_XX 10 (Integer_Literal 1) (**(nil)**)))))) 
      (D_Object_Declaration_XX 11 (mkobject_declaration_xx 12 ((*T*) 4) Integer None))))
        (* Procedure Body *)
          (S_Sequence_XX 13
          (S_Assignment_XX 14 (E_Identifier_XX 15 ((*T*) 4) (**(nil)**)) (E_Name_XX 16 (E_Identifier_XX 17 ((*N*) 1) (**(nil)**)) (**(nil)**))) 
          (S_Sequence_XX 18
          (S_While_Loop_XX 19 (E_Binary_Operation_XX 20 Greater_Than (E_Name_XX 21 (E_Identifier_XX 22 ((*T*) 4) (**(nil)**)) (**(nil)**)) (E_Literal_XX 23 (Integer_Literal 0) (**(nil)**)) (**(nil)**))
            (S_Sequence_XX 24
            (S_Assignment_XX 25 (E_Identifier_XX 26 ((*Result*) 3) (**(nil)**)) (E_Binary_Operation_XX 27 Multiply (E_Name_XX 28 (E_Identifier_XX 29 ((*Result*) 3) (**(nil)**)) (**(nil)**)) (E_Name_XX 30 (E_Identifier_XX 31 ((*T*) 4) (**(nil)**)) (**(nil)**)) (**(Do_Overflow_Check :: nil)**))) 
            (S_Assignment_XX 32 (E_Identifier_XX 33 ((*T*) 4) (**(nil)**)) (E_Binary_Operation_XX 34 Minus (E_Name_XX 35 (E_Identifier_XX 36 ((*T*) 4) (**(nil)**)) (**(nil)**)) (E_Literal_XX 37 (Integer_Literal 1) (**(nil)**)) (**(Do_Overflow_Check :: nil)**))))
          ) 
          (S_Assignment_XX 38 (E_Identifier_XX 39 ((*M*) 2) (**(nil)**)) (E_Name_XX 40 (E_Identifier_XX 41 ((*Result*) 3) (**(nil)**)) (**(nil)**)))))
      )
    )
  )
 .