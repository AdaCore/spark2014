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
        ((*Test*) 1)
        (* Procedure Contract *)
        (nil)
        (* Formal Parameters *)
        (
        (mkparameter_specification_xx 5 ((*N*) 1) In Integer) :: 
        (mkparameter_specification_xx 6 ((*M*) 2) Out Integer) :: nil) 
        (* Object Declarations *)
        (
        (D_Type_Declaration_XX 7 (Record_Type_Declaration_XX 8 ((*RecordT*) 1) ((((*X*) 3), Integer) :: nil))) :: 
        (D_Type_Declaration_XX 10 (Array_Type_Declaration_XX 11 ((*ArrayT*) 2) ((*componentType*) Integer) ((*lowerBound*) 0) ((*upperBound*) 5))) :: 
        (D_Procedure_Declaration_XX 12 (mkprocedure_declaration_xx 13
          (* Procedure Name *)
          ((*Increase*) 2)
          (* Procedure Contract *)
          (nil)
          (* Formal Parameters *)
          (
          (mkparameter_specification_xx 14 ((*X*) 4) In Integer) :: 
          (mkparameter_specification_xx 15 ((*Y*) 5) Out Integer) :: nil) 
          (* Object Declarations *)
          (nil)
          (* Procedure Body *)
            (S_Assignment_XX 16 (E_Identifier_XX 17 ((*Y*) 5) (**(nil)**)) (E_Binary_Operation_XX 18 Plus (E_Name_XX 19 (E_Identifier_XX 20 ((*X*) 4) (**(nil)**)) (**(nil)**)) (E_Literal_XX 21 (Integer_Literal 1) (**(nil)**)) (**(Do_Overflow_Check :: nil)**)))
        )) :: 
        (D_Object_Declaration_XX 22 (mkobject_declaration_xx 23 ((*R*) 6) (Aggregate ((*RecordT*) 1)) None)) :: 
        (D_Object_Declaration_XX 24 (mkobject_declaration_xx 25 ((*A*) 7) (Aggregate ((*ArrayT*) 2)) None)) :: 
        (D_Object_Declaration_XX 26 (mkobject_declaration_xx 27 ((*Result*) 8) Integer (Some ((E_Literal_XX 28 (Integer_Literal 1) (**(nil)**)))))) :: 
        (D_Object_Declaration_XX 29 (mkobject_declaration_xx 30 ((*T*) 9) Integer (Some ((E_Name_XX 31 (E_Identifier_XX 32 ((*Result*) 8) (**(nil)**)) (**(nil)**)))))) :: 
        (D_Object_Declaration_XX 33 (mkobject_declaration_xx 34 ((*T1*) 10) Integer None)) :: 
        (D_Object_Declaration_XX 35 (mkobject_declaration_xx 36 ((*T2*) 11) Integer None)) :: nil)
        (* Procedure Body *)
          (S_Sequence_XX 37
          (S_Assignment_XX 38 (E_Selected_Component_XX 39 40 ((*R*) 6) ((*X*) 3) (**(nil)**)) (E_Literal_XX 43 (Integer_Literal 1) (**(nil)**))) 
          (S_Sequence_XX 44
          (S_Assignment_XX 45 (E_Indexed_Component_XX 46 47 ((*A*) 7) (E_Literal_XX 49 (Integer_Literal 0) (**(nil)**)) (**(nil)**)) (E_Literal_XX 50 (Integer_Literal 1) (**(nil)**))) 
          (S_Sequence_XX 51
          (S_Assignment_XX 52 (E_Identifier_XX 53 ((*T1*) 10) (**(nil)**)) (E_Binary_Operation_XX 54 Plus (E_Name_XX 55 (E_Selected_Component_XX 56 57 ((*R*) 6) ((*X*) 3) (**(nil)**)) (**(nil)**)) (E_Name_XX 60 (E_Identifier_XX 61 ((*N*) 1) (**(nil)**)) (**(nil)**)) (**(Do_Overflow_Check :: nil)**))) 
          (S_Sequence_XX 62
          (S_Assignment_XX 63 (E_Identifier_XX 64 ((*T2*) 11) (**(nil)**)) (E_Binary_Operation_XX 65 Plus (E_Name_XX 66 (E_Indexed_Component_XX 67 68 ((*A*) 7) (E_Literal_XX 70 (Integer_Literal 0) (**(nil)**)) (**(nil)**)) (**(nil)**)) (E_Name_XX 71 (E_Identifier_XX 72 ((*T1*) 10) (**(nil)**)) (**(nil)**)) (**(Do_Overflow_Check :: nil)**))) 
          (S_Sequence_XX 73
          (S_Assignment_XX 74 (E_Identifier_XX 75 ((*T*) 9) (**(nil)**)) (E_Name_XX 76 (E_Identifier_XX 77 ((*T2*) 11) (**(nil)**)) (**(nil)**))) 
          (S_Sequence_XX 78
          (S_Procedure_Call_XX 79 80 ((*Increase*) 2) 
            ((E_Name_XX 81 (E_Identifier_XX 82 ((*T2*) 11) (**(nil)**)) (**(nil)**)) :: (E_Name_XX 83 (E_Identifier_XX 84 ((*T*) 9) (**(nil)**)) (**(nil)**)) :: nil)
          ) 
          (S_Sequence_XX 85
          (S_If_XX 86 (E_Binary_Operation_XX 87 Greater_Than (E_Name_XX 88 (E_Identifier_XX 89 ((*T*) 9) (**(nil)**)) (**(nil)**)) (E_Literal_XX 90 (Integer_Literal 0) (**(nil)**)) (**(nil)**))
            (S_Assignment_XX 91 (E_Identifier_XX 92 ((*T*) 9) (**(nil)**)) (E_Binary_Operation_XX 93 Plus (E_Name_XX 94 (E_Identifier_XX 95 ((*T*) 9) (**(nil)**)) (**(nil)**)) (E_Literal_XX 96 (Integer_Literal 1) (**(nil)**)) (**(Do_Overflow_Check :: nil)**)))
            S_Null_XX
          ) 
          (S_Sequence_XX 97
          (S_If_XX 98 (E_Binary_Operation_XX 99 Greater_Than (E_Name_XX 100 (E_Identifier_XX 101 ((*T*) 9) (**(nil)**)) (**(nil)**)) (E_Literal_XX 102 (Integer_Literal 1) (**(nil)**)) (**(nil)**))
            (S_Assignment_XX 103 (E_Identifier_XX 104 ((*T*) 9) (**(nil)**)) (E_Binary_Operation_XX 105 Plus (E_Name_XX 106 (E_Identifier_XX 107 ((*T*) 9) (**(nil)**)) (**(nil)**)) (E_Literal_XX 108 (Integer_Literal 2) (**(nil)**)) (**(Do_Overflow_Check :: nil)**)))
            (S_Assignment_XX 109 (E_Identifier_XX 110 ((*T*) 9) (**(nil)**)) (E_Binary_Operation_XX 111 Minus (E_Name_XX 112 (E_Identifier_XX 113 ((*T*) 9) (**(nil)**)) (**(nil)**)) (E_Literal_XX 114 (Integer_Literal 1) (**(nil)**)) (**(Do_Overflow_Check :: nil)**)))
          ) 
          (S_Sequence_XX 115
          (S_While_Loop_XX 116 (E_Binary_Operation_XX 117 Greater_Than (E_Name_XX 118 (E_Identifier_XX 119 ((*T*) 9) (**(nil)**)) (**(nil)**)) (E_Literal_XX 120 (Integer_Literal 0) (**(nil)**)) (**(nil)**))
            (S_Sequence_XX 121
            (S_Assignment_XX 122 (E_Identifier_XX 123 ((*Result*) 8) (**(nil)**)) (E_Binary_Operation_XX 124 Divide (E_Binary_Operation_XX 125 Multiply (E_Name_XX 126 (E_Identifier_XX 127 ((*Result*) 8) (**(nil)**)) (**(nil)**)) (E_Name_XX 128 (E_Identifier_XX 129 ((*T*) 9) (**(nil)**)) (**(nil)**)) (**(Do_Overflow_Check :: nil)**)) (E_Name_XX 130 (E_Identifier_XX 131 ((*N*) 1) (**(nil)**)) (**(nil)**)) (**(Do_Division_Check :: Do_Overflow_Check :: nil)**))) 
            (S_Assignment_XX 132 (E_Identifier_XX 133 ((*T*) 9) (**(nil)**)) (E_Binary_Operation_XX 134 Minus (E_Name_XX 135 (E_Identifier_XX 136 ((*T*) 9) (**(nil)**)) (**(nil)**)) (E_Literal_XX 137 (Integer_Literal 1) (**(nil)**)) (**(Do_Overflow_Check :: nil)**))))
          ) 
          (S_Assignment_XX 138 (E_Identifier_XX 139 ((*M*) 2) (**(nil)**)) (E_Name_XX 140 (E_Identifier_XX 141 ((*Result*) 8) (**(nil)**)) (**(nil)**))))))))))))
      )
    )
  )
 .