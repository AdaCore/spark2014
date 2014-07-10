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
        ((*Test*) 1)
        (* Procedure Contract *)
        (nil)
        (* Formal Parameters *)
        (
        (mkparameter_specification_x 5 ((*N*) 1) In Integer) :: 
        (mkparameter_specification_x 6 ((*M*) 2) Out Integer) :: nil) 
        (* Object Declarations *)
        (
        (D_Type_Declaration_X 7 (Record_Type_Declaration_X 8 ((*RecordT*) 1) ((((*X*) 3), Integer) :: nil))) :: 
        (D_Type_Declaration_X 10 (Array_Type_Declaration_X 11 ((*ArrayT*) 2) ((*componentType*) Integer) ((*lowerBound*) 0) ((*upperBound*) 5))) :: 
        (D_Procedure_Declaration_X 12 (mkprocedure_declaration_x 13
          (* Procedure Name *)
          ((*Increase*) 2)
          (* Procedure Contract *)
          (nil)
          (* Formal Parameters *)
          (
          (mkparameter_specification_x 14 ((*X*) 4) In Integer) :: 
          (mkparameter_specification_x 15 ((*Y*) 5) Out Integer) :: nil) 
          (* Object Declarations *)
          (nil)
          (* Procedure Body *)
            (S_Assignment_X 16 (E_Identifier_X 17 ((*Y*) 5) (nil)) (E_Binary_Operation_X 18 Plus (E_Name_X 19 (E_Identifier_X 20 ((*X*) 4) (nil)) (nil)) (E_Literal_X 21 (Integer_Literal 1) (nil)) (Do_Overflow_Check :: nil)))
        )) :: 
        (D_Object_Declaration_X 22 (mkobject_declaration_x 23 ((*R*) 6) (Aggregate ((*RecordT*) 1)) None)) :: 
        (D_Object_Declaration_X 24 (mkobject_declaration_x 25 ((*A*) 7) (Aggregate ((*ArrayT*) 2)) None)) :: 
        (D_Object_Declaration_X 26 (mkobject_declaration_x 27 ((*Result*) 8) Integer (Some ((E_Literal_X 28 (Integer_Literal 1) (nil)))))) :: 
        (D_Object_Declaration_X 29 (mkobject_declaration_x 30 ((*T*) 9) Integer (Some ((E_Name_X 31 (E_Identifier_X 32 ((*Result*) 8) (nil)) (nil)))))) :: 
        (D_Object_Declaration_X 33 (mkobject_declaration_x 34 ((*T1*) 10) Integer None)) :: 
        (D_Object_Declaration_X 35 (mkobject_declaration_x 36 ((*T2*) 11) Integer None)) :: nil)
        (* Procedure Body *)
          (S_Sequence_X 37
          (S_Assignment_X 38 (E_Selected_Component_X 39 40 ((*R*) 6) ((*X*) 3) (nil)) (E_Literal_X 43 (Integer_Literal 1) (nil))) 
          (S_Sequence_X 44
          (S_Assignment_X 45 (E_Indexed_Component_X 46 47 ((*A*) 7) (E_Literal_X 49 (Integer_Literal 0) (nil)) (nil)) (E_Literal_X 50 (Integer_Literal 1) (nil))) 
          (S_Sequence_X 51
          (S_Assignment_X 52 (E_Identifier_X 53 ((*T1*) 10) (nil)) (E_Binary_Operation_X 54 Plus (E_Name_X 55 (E_Selected_Component_X 56 57 ((*R*) 6) ((*X*) 3) (nil)) (nil)) (E_Name_X 60 (E_Identifier_X 61 ((*N*) 1) (nil)) (nil)) (Do_Overflow_Check :: nil))) 
          (S_Sequence_X 62
          (S_Assignment_X 63 (E_Identifier_X 64 ((*T2*) 11) (nil)) (E_Binary_Operation_X 65 Plus (E_Name_X 66 (E_Indexed_Component_X 67 68 ((*A*) 7) (E_Literal_X 70 (Integer_Literal 0) (nil)) (nil)) (nil)) (E_Name_X 71 (E_Identifier_X 72 ((*T1*) 10) (nil)) (nil)) (Do_Overflow_Check :: nil))) 
          (S_Sequence_X 73
          (S_Assignment_X 74 (E_Identifier_X 75 ((*T*) 9) (nil)) (E_Name_X 76 (E_Identifier_X 77 ((*T2*) 11) (nil)) (nil))) 
          (S_Sequence_X 78
          (S_Procedure_Call_X 79 80 ((*Increase*) 2) 
            ((E_Name_X 81 (E_Identifier_X 82 ((*T2*) 11) (nil)) (nil)) :: (E_Name_X 83 (E_Identifier_X 84 ((*T*) 9) (nil)) (nil)) :: nil)
          ) 
          (S_Sequence_X 85
          (S_If_X 86 (E_Binary_Operation_X 87 Greater_Than (E_Name_X 88 (E_Identifier_X 89 ((*T*) 9) (nil)) (nil)) (E_Literal_X 90 (Integer_Literal 0) (nil)) (nil))
            (S_Assignment_X 91 (E_Identifier_X 92 ((*T*) 9) (nil)) (E_Binary_Operation_X 93 Plus (E_Name_X 94 (E_Identifier_X 95 ((*T*) 9) (nil)) (nil)) (E_Literal_X 96 (Integer_Literal 1) (nil)) (Do_Overflow_Check :: nil)))
            S_Null_X
          ) 
          (S_Sequence_X 97
          (S_If_X 98 (E_Binary_Operation_X 99 Greater_Than (E_Name_X 100 (E_Identifier_X 101 ((*T*) 9) (nil)) (nil)) (E_Literal_X 102 (Integer_Literal 1) (nil)) (nil))
            (S_Assignment_X 103 (E_Identifier_X 104 ((*T*) 9) (nil)) (E_Binary_Operation_X 105 Plus (E_Name_X 106 (E_Identifier_X 107 ((*T*) 9) (nil)) (nil)) (E_Literal_X 108 (Integer_Literal 2) (nil)) (Do_Overflow_Check :: nil)))
            (S_Assignment_X 109 (E_Identifier_X 110 ((*T*) 9) (nil)) (E_Binary_Operation_X 111 Minus (E_Name_X 112 (E_Identifier_X 113 ((*T*) 9) (nil)) (nil)) (E_Literal_X 114 (Integer_Literal 1) (nil)) (Do_Overflow_Check :: nil)))
          ) 
          (S_Sequence_X 115
          (S_While_Loop_X 116 (E_Binary_Operation_X 117 Greater_Than (E_Name_X 118 (E_Identifier_X 119 ((*T*) 9) (nil)) (nil)) (E_Literal_X 120 (Integer_Literal 0) (nil)) (nil))
            (S_Sequence_X 121
            (S_Assignment_X 122 (E_Identifier_X 123 ((*Result*) 8) (nil)) (E_Binary_Operation_X 124 Divide (E_Binary_Operation_X 125 Multiply (E_Name_X 126 (E_Identifier_X 127 ((*Result*) 8) (nil)) (nil)) (E_Name_X 128 (E_Identifier_X 129 ((*T*) 9) (nil)) (nil)) (Do_Overflow_Check :: nil)) (E_Name_X 130 (E_Identifier_X 131 ((*N*) 1) (nil)) (nil)) (Do_Division_Check :: Do_Overflow_Check :: nil))) 
            (S_Assignment_X 132 (E_Identifier_X 133 ((*T*) 9) (nil)) (E_Binary_Operation_X 134 Minus (E_Name_X 135 (E_Identifier_X 136 ((*T*) 9) (nil)) (nil)) (E_Literal_X 137 (Integer_Literal 1) (nil)) (Do_Overflow_Check :: nil))))
          ) 
          (S_Assignment_X 138 (E_Identifier_X 139 ((*M*) 2) (nil)) (E_Name_X 140 (E_Identifier_X 141 ((*Result*) 8) (nil)) (nil))))))))))))
      )
    )
  )
 .
