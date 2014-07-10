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
        ((*Test*) 1)
        (* Procedure Contract *)
        (nil)
        (* Formal Parameters *)
        (
        (mkparameter_specification 5 ((*N*) 1) In Integer) :: 
        (mkparameter_specification 6 ((*M*) 2) Out Integer) :: nil) 
        (* Object Declarations *)
        (
        (D_Type_Declaration 7 (Record_Type_Declaration 8 ((*RecordT*) 1) ((((*X*) 3), Integer) :: nil))) :: 
        (D_Type_Declaration 10 (Array_Type_Declaration 11 ((*ArrayT*) 2) ((*componentType*) Integer) ((*lowerBound*) 0) ((*upperBound*) 5))) :: 
        (D_Procedure_Declaration 12 (mkprocedure_declaration 13
          (* Procedure Name *)
          ((*Increase*) 2)
          (* Procedure Contract *)
          (nil)
          (* Formal Parameters *)
          (
          (mkparameter_specification 14 ((*X*) 4) In Integer) :: 
          (mkparameter_specification 15 ((*Y*) 5) Out Integer) :: nil) 
          (* Object Declarations *)
          (nil)
          (* Procedure Body *)
            (S_Assignment 16 (E_Identifier 17 ((*Y*) 5) (**(nil)**)) (E_Binary_Operation 18 Plus (E_Name 19 (E_Identifier 20 ((*X*) 4) (**(nil)**)) (**(nil)**)) (E_Literal 21 (Integer_Literal 1) (**(nil)**)) (**(Do_Overflow_Check :: nil)**)))
        )) :: 
        (D_Object_Declaration 22 (mkobject_declaration 23 ((*R*) 6) (Aggregate ((*RecordT*) 1)) None)) :: 
        (D_Object_Declaration 24 (mkobject_declaration 25 ((*A*) 7) (Aggregate ((*ArrayT*) 2)) None)) :: 
        (D_Object_Declaration 26 (mkobject_declaration 27 ((*Result*) 8) Integer (Some ((E_Literal 28 (Integer_Literal 1) (**(nil)**)))))) :: 
        (D_Object_Declaration 29 (mkobject_declaration 30 ((*T*) 9) Integer (Some ((E_Name 31 (E_Identifier 32 ((*Result*) 8) (**(nil)**)) (**(nil)**)))))) :: 
        (D_Object_Declaration 33 (mkobject_declaration 34 ((*T1*) 10) Integer None)) :: 
        (D_Object_Declaration 35 (mkobject_declaration 36 ((*T2*) 11) Integer None)) :: nil)
        (* Procedure Body *)
          (S_Sequence 37
          (S_Assignment 38 (E_Selected_Component 39 40 ((*R*) 6) ((*X*) 3) (**(nil)**)) (E_Literal 43 (Integer_Literal 1) (**(nil)**))) 
          (S_Sequence 44
          (S_Assignment 45 (E_Indexed_Component 46 47 ((*A*) 7) (E_Literal 49 (Integer_Literal 0) (**(nil)**)) (**(nil)**)) (E_Literal 50 (Integer_Literal 1) (**(nil)**))) 
          (S_Sequence 51
          (S_Assignment 52 (E_Identifier 53 ((*T1*) 10) (**(nil)**)) (E_Binary_Operation 54 Plus (E_Name 55 (E_Selected_Component 56 57 ((*R*) 6) ((*X*) 3) (**(nil)**)) (**(nil)**)) (E_Name 60 (E_Identifier 61 ((*N*) 1) (**(nil)**)) (**(nil)**)) (**(Do_Overflow_Check :: nil)**))) 
          (S_Sequence 62
          (S_Assignment 63 (E_Identifier 64 ((*T2*) 11) (**(nil)**)) (E_Binary_Operation 65 Plus (E_Name 66 (E_Indexed_Component 67 68 ((*A*) 7) (E_Literal 70 (Integer_Literal 0) (**(nil)**)) (**(nil)**)) (**(nil)**)) (E_Name 71 (E_Identifier 72 ((*T1*) 10) (**(nil)**)) (**(nil)**)) (**(Do_Overflow_Check :: nil)**))) 
          (S_Sequence 73
          (S_Assignment 74 (E_Identifier 75 ((*T*) 9) (**(nil)**)) (E_Name 76 (E_Identifier 77 ((*T2*) 11) (**(nil)**)) (**(nil)**))) 
          (S_Sequence 78
          (S_Procedure_Call 79 80 ((*Increase*) 2) 
            ((E_Name 81 (E_Identifier 82 ((*T2*) 11) (**(nil)**)) (**(nil)**)) :: (E_Name 83 (E_Identifier 84 ((*T*) 9) (**(nil)**)) (**(nil)**)) :: nil)
          ) 
          (S_Sequence 85
          (S_If 86 (E_Binary_Operation 87 Greater_Than (E_Name 88 (E_Identifier 89 ((*T*) 9) (**(nil)**)) (**(nil)**)) (E_Literal 90 (Integer_Literal 0) (**(nil)**)) (**(nil)**))
            (S_Assignment 91 (E_Identifier 92 ((*T*) 9) (**(nil)**)) (E_Binary_Operation 93 Plus (E_Name 94 (E_Identifier 95 ((*T*) 9) (**(nil)**)) (**(nil)**)) (E_Literal 96 (Integer_Literal 1) (**(nil)**)) (**(Do_Overflow_Check :: nil)**)))
            S_Null
          ) 
          (S_Sequence 97
          (S_If 98 (E_Binary_Operation 99 Greater_Than (E_Name 100 (E_Identifier 101 ((*T*) 9) (**(nil)**)) (**(nil)**)) (E_Literal 102 (Integer_Literal 1) (**(nil)**)) (**(nil)**))
            (S_Assignment 103 (E_Identifier 104 ((*T*) 9) (**(nil)**)) (E_Binary_Operation 105 Plus (E_Name 106 (E_Identifier 107 ((*T*) 9) (**(nil)**)) (**(nil)**)) (E_Literal 108 (Integer_Literal 2) (**(nil)**)) (**(Do_Overflow_Check :: nil)**)))
            (S_Assignment 109 (E_Identifier 110 ((*T*) 9) (**(nil)**)) (E_Binary_Operation 111 Minus (E_Name 112 (E_Identifier 113 ((*T*) 9) (**(nil)**)) (**(nil)**)) (E_Literal 114 (Integer_Literal 1) (**(nil)**)) (**(Do_Overflow_Check :: nil)**)))
          ) 
          (S_Sequence 115
          (S_While_Loop 116 (E_Binary_Operation 117 Greater_Than (E_Name 118 (E_Identifier 119 ((*T*) 9) (**(nil)**)) (**(nil)**)) (E_Literal 120 (Integer_Literal 0) (**(nil)**)) (**(nil)**))
            (S_Sequence 121
            (S_Assignment 122 (E_Identifier 123 ((*Result*) 8) (**(nil)**)) (E_Binary_Operation 124 Divide (E_Binary_Operation 125 Multiply (E_Name 126 (E_Identifier 127 ((*Result*) 8) (**(nil)**)) (**(nil)**)) (E_Name 128 (E_Identifier 129 ((*T*) 9) (**(nil)**)) (**(nil)**)) (**(Do_Overflow_Check :: nil)**)) (E_Name 130 (E_Identifier 131 ((*N*) 1) (**(nil)**)) (**(nil)**)) (**(Do_Division_Check :: Do_Overflow_Check :: nil)**))) 
            (S_Assignment 132 (E_Identifier 133 ((*T*) 9) (**(nil)**)) (E_Binary_Operation 134 Minus (E_Name 135 (E_Identifier 136 ((*T*) 9) (**(nil)**)) (**(nil)**)) (E_Literal 137 (Integer_Literal 1) (**(nil)**)) (**(Do_Overflow_Check :: nil)**))))
          ) 
          (S_Assignment 138 (E_Identifier 139 ((*M*) 2) (**(nil)**)) (E_Name 140 (E_Identifier 141 ((*Result*) 8) (**(nil)**)) (**(nil)**))))))))))))
      )
    )
  )
 .
