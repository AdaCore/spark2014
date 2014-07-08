Require Import language_flagged.

Definition p := 

    Library_Subprogram 2 (
      (* Procedure Body Declaration *)
      Global_Procedure_XX 3 (
        mkprocedure_declaration_xx 4
          (* Procedure Body - Name *)
          ((*Test*) 1)
          (* Procedure Body - Specification *)
          (nil)
          (* Procedure Body - Parameters *)
          (
          mkparameter_specification_xx 5 ((*N*) 1) (((*Integer*) 1)) In :: 
          mkparameter_specification_xx 6 ((*M*) 2) (((*Integer*) 1)) Out :: nil) 
          (* Procedure Body - Variable Declarations *)
          (
          (Record_Type_Declaration_XX 7 ((*RecordT*) 2) (((*X*) 3), ((*Integer*) 1)) :: nil) :: 
          (Array_Type_Declaration_XX 9 ((*ArrayT*) 3) ((*Integer*) 1) 0 5) :: 
          (* Procedure Body Declaration *)
          Global_Procedure_XX 10 (
            mkprocedure_declaration_xx 11
              (* Procedure Body - Name *)
              ((*Increase*) 2)
              (* Procedure Body - Specification *)
              (nil)
              (* Procedure Body - Parameters *)
              (
              mkparameter_specification_xx 12 ((*X*) 4) (((*Integer*) 1)) In :: 
              mkparameter_specification_xx 13 ((*Y*) 5) (((*Integer*) 1)) Out :: nil) 
              (* Procedure Body - Variable Declarations *)
              (nil)
              (* Procedure Body - Statements *) (
                (S_Assignment_XX 14 (E_Identifier_XX 15 ((*Y*) 5) (*checks*)) (E_Binary_Operation_XX 16 Plus (E_Name_XX 17 (E_Identifier_XX 18 ((*X*) 4) (*checks*)) (*checks*)) (E_Literal_XX 19 (Integer_Literal 1) (*nil*)) (*checks*)))
              )
          ) :: 
          mkobject_declaration_xx 20 ((*R*) 6) ((*RecordT*) 2) None :: 
          mkobject_declaration_xx 21 ((*A*) 7) ((*ArrayT*) 3) None :: 
          mkobject_declaration_xx 22 ((*Result*) 8) ((*Integer*) 1) (Some ((E_Literal_XX 23 (Integer_Literal 1) (*nil*)))) :: 
          mkobject_declaration_xx 24 ((*T*) 9) ((*Integer*) 1) (Some ((E_Name_XX 25 (E_Identifier_XX 26 ((*Result*) 8) (*checks*)) (*checks*)))) :: 
          mkobject_declaration_xx 27 ((*T1*) 10) ((*Integer*) 1) None :: 
          mkobject_declaration_xx 28 ((*T2*) 11) ((*Integer*) 1) None :: nil)
          (* Procedure Body - Statements *) (
            (S_Sequence_XX 29
              (S_Assignment_XX 30 (E_Selected_Component_XX 31 32 ((*R*) 6) ((*X*) 3) (*checks*)) (E_Literal_XX 35 (Integer_Literal 1) (*nil*))) 
              (S_Sequence_XX 36
                (S_Assignment_XX 37 (E_Indexed_Component_XX 38 39 ((*A*) 7) (E_Literal_XX 41 (Integer_Literal 0) (*nil*)) (*checks*)) (E_Literal_XX 42 (Integer_Literal 1) (*nil*))) 
                (S_Sequence_XX 43
                  (S_Assignment_XX 44 (E_Identifier_XX 45 ((*T1*) 10) (*checks*)) (E_Binary_Operation_XX 46 Plus (E_Name_XX 47 (E_Selected_Component_XX 48 49 ((*R*) 6) ((*X*) 3) (*checks*)) (*checks*)) (E_Name_XX 52 (E_Identifier_XX 53 ((*N*) 1) (*checks*)) (*checks*)) (*checks*))) 
                  (S_Sequence_XX 54
                    (S_Assignment_XX 55 (E_Identifier_XX 56 ((*T2*) 11) (*checks*)) (E_Binary_Operation_XX 57 Plus (E_Name_XX 58 (E_Indexed_Component_XX 59 60 ((*A*) 7) (E_Literal_XX 62 (Integer_Literal 0) (*nil*)) (*checks*)) (*checks*)) (E_Name_XX 63 (E_Identifier_XX 64 ((*T1*) 10) (*checks*)) (*checks*)) (*checks*))) 
                    (S_Sequence_XX 65
                      (S_Assignment_XX 66 (E_Identifier_XX 67 ((*T*) 9) (*checks*)) (E_Name_XX 68 (E_Identifier_XX 69 ((*T2*) 11) (*checks*)) (*checks*))) 
                      (S_Sequence_XX 70
                        (S_Procedure_Call_XX 71 72 ((*Increase*) 2) 
                          (E_Name_XX 73 (E_Identifier_XX 74 ((*T2*) 11) (*checks*)) (*checks*)) :: (E_Name_XX 75 (E_Identifier_XX 76 ((*T*) 9) (*checks*)) (*checks*)) :: nil
                        ) 
                        (S_Sequence_XX 77
                          (S_If_XX 78 (E_Binary_Operation_XX 79 Greater_Than (E_Name_XX 80 (E_Identifier_XX 81 ((*T*) 9) (*checks*)) (*checks*)) (E_Literal_XX 82 (Integer_Literal 0) (*nil*)) (*checks*))
                            (S_Assignment_XX 83 (E_Identifier_XX 84 ((*T*) 9) (*checks*)) (E_Binary_Operation_XX 85 Plus (E_Name_XX 86 (E_Identifier_XX 87 ((*T*) 9) (*checks*)) (*checks*)) (E_Literal_XX 88 (Integer_Literal 1) (*nil*)) (*checks*)))
                            S_Null_XX
                          ) 
                          (S_Sequence_XX 89
                            (S_If_XX 90 (E_Binary_Operation_XX 91 Greater_Than (E_Name_XX 92 (E_Identifier_XX 93 ((*T*) 9) (*checks*)) (*checks*)) (E_Literal_XX 94 (Integer_Literal 1) (*nil*)) (*checks*))
                              (S_Assignment_XX 95 (E_Identifier_XX 96 ((*T*) 9) (*checks*)) (E_Binary_Operation_XX 97 Plus (E_Name_XX 98 (E_Identifier_XX 99 ((*T*) 9) (*checks*)) (*checks*)) (E_Literal_XX 100 (Integer_Literal 2) (*nil*)) (*checks*)))
                              (S_Assignment_XX 101 (E_Identifier_XX 102 ((*T*) 9) (*checks*)) (E_Binary_Operation_XX 103 Minus (E_Name_XX 104 (E_Identifier_XX 105 ((*T*) 9) (*checks*)) (*checks*)) (E_Literal_XX 106 (Integer_Literal 1) (*nil*)) (*checks*)))
                            ) 
                            (S_Sequence_XX 107
                              (S_While_Loop_XX 108 (E_Binary_Operation_XX 109 Greater_Than (E_Name_XX 110 (E_Identifier_XX 111 ((*T*) 9) (*checks*)) (*checks*)) (E_Literal_XX 112 (Integer_Literal 0) (*nil*)) (*checks*))
                                (S_Sequence_XX 113
                                  (S_Assignment_XX 114 (E_Identifier_XX 115 ((*Result*) 8) (*checks*)) (E_Binary_Operation_XX 116 Divide (E_Binary_Operation_XX 117 Multiply (E_Name_XX 118 (E_Identifier_XX 119 ((*Result*) 8) (*checks*)) (*checks*)) (E_Name_XX 120 (E_Identifier_XX 121 ((*T*) 9) (*checks*)) (*checks*)) (*checks*)) (E_Name_XX 122 (E_Identifier_XX 123 ((*N*) 1) (*checks*)) (*checks*)) (*checks*))) 
                                  (S_Assignment_XX 124 (E_Identifier_XX 125 ((*T*) 9) (*checks*)) (E_Binary_Operation_XX 126 Minus (E_Name_XX 127 (E_Identifier_XX 128 ((*T*) 9) (*checks*)) (*checks*)) (E_Literal_XX 129 (Integer_Literal 1) (*nil*)) (*checks*)))
                                )
                              ) 
                              (S_Assignment_XX 130 (E_Identifier_XX 131 ((*M*) 2) (*checks*)) (E_Name_XX 132 (E_Identifier_XX 133 ((*Result*) 8) (*checks*)) (*checks*)))
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
      )
    )
  .