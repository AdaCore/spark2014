Require Import language_flagged.

Definition x := (Record_Type_Declaration 7 ((*RecordT*) 2) ((((*X*) 3), ((*Integer*) Integer)) :: nil)).

Definition p := 
    Library_Subprogram 2 (
      (* Procedure Body Declaration *)
      Global_Procedure 3 (
        mkprocedure_declaration 4
          (* Procedure Body - Name *)
          ((*Test*) 1)
          (* Procedure Body - Specification *)
          (nil)
          (* Procedure Body - Parameters *)
          (
          mkparameter_specification 5 ((*N*) 1) (((*Integer*) Integer)) In :: 
          mkparameter_specification 6 ((*M*) 2) (((*Integer*) Integer)) Out :: nil) 
          (* Procedure Body - Variable Declarations *)
          (
          (Record_Type_Declaration 7 ((*RecordT*) 2) ((((*X*) 3), ((*Integer*) Integer)) :: nil)) :: 
          (Array_Type_Declaration 9 ((*ArrayT*) 3) ((*Integer*) Integer) 0 5) :: 
          (* Procedure Body Declaration *)
          (Global_Procedure 10 (
            mkprocedure_declaration 11
              (* Procedure Body - Name *)
              ((*Increase*) 2)
              (* Procedure Body - Specification *)
              (nil)
              (* Procedure Body - Parameters *)
              (
              mkparameter_specification 12 ((*X*) 4) (((*Integer*) Integer)) In :: 
              mkparameter_specification 13 ((*Y*) 5) (((*Integer*) Integer)) Out :: nil) 
              (* Procedure Body - Variable Declarations *)
              (nil)
              (* Procedure Body - Statements *) (
                (S_Assignment 14 (E_Identifier 15 ((*Y*) 5) ) (E_Binary_Operation 16 Plus (E_Name 17 (E_Identifier 18 ((*X*) 4) ) ) (E_Literal 19 (Integer_Literal 1) (*nil*)) ))
              )
          )) :: 
          (mkobject_declaration 20 ((*R*) 6) ((*RecordT*) Integer) None) :: 
          mkobject_declaration 21 ((*A*) 7) ((*ArrayT*) Integer) None :: 
          mkobject_declaration 22 ((*Result*) 8) ((*Integer*) Integer) (Some ((E_Literal 23 (Integer_Literal 1) (*nil*)))) :: 
          mkobject_declaration 24 ((*T*) 9) ((*Integer*) Integer) (Some ((E_Name 25 (E_Identifier 26 ((*Result*) 8) ) ))) :: 
          mkobject_declaration 27 ((*T1*) 10) ((*Integer*) Integer) None :: 
          mkobject_declaration 28 ((*T2*) 11) ((*Integer*) Integer) None :: nil)
          (* Procedure Body - Statements *) (
            (S_Sequence 29
              (S_Assignment 30 (E_Selected_Component 31 32 ((*R*) 6) ((*X*) 3) ) (E_Literal 35 (Integer_Literal 1) (*nil*))) 
              (S_Sequence 36
                (S_Assignment 37 (E_Indexed_Component 38 39 ((*A*) 7) (E_Literal 41 (Integer_Literal 0) (*nil*)) ) (E_Literal 42 (Integer_Literal 1) (*nil*))) 
                (S_Sequence 43
                  (S_Assignment 44 (E_Identifier 45 ((*T1*) 10) ) (E_Binary_Operation 46 Plus (E_Name 47 (E_Selected_Component 48 49 ((*R*) 6) ((*X*) 3) ) ) (E_Name 52 (E_Identifier 53 ((*N*) 1) ) ) )) 
                  (S_Sequence 54
                    (S_Assignment 55 (E_Identifier 56 ((*T2*) 11) ) (E_Binary_Operation 57 Plus (E_Name 58 (E_Indexed_Component 59 60 ((*A*) 7) (E_Literal 62 (Integer_Literal 0) (*nil*)) ) ) (E_Name 63 (E_Identifier 64 ((*T1*) 10) ) ) )) 
                    (S_Sequence 65
                      (S_Assignment 66 (E_Identifier 67 ((*T*) 9) ) (E_Name 68 (E_Identifier 69 ((*T2*) 11) ) )) 
                      (S_Sequence 70
                        (S_Procedure_Call 71 72 ((*Increase*) 2) 
                          (E_Name 73 (E_Identifier 74 ((*T2*) 11) ) ) :: (E_Name 75 (E_Identifier 76 ((*T*) 9) ) ) :: nil
                        ) 
                        (S_Sequence 77
                          (S_If 78 (E_Binary_Operation 79 Greater_Than (E_Name 80 (E_Identifier 81 ((*T*) 9) ) ) (E_Literal 82 (Integer_Literal 0) (*nil*)) )
                            (S_Assignment 83 (E_Identifier 84 ((*T*) 9) ) (E_Binary_Operation 85 Plus (E_Name 86 (E_Identifier 87 ((*T*) 9) ) ) (E_Literal 88 (Integer_Literal 1) (*nil*)) ))
                            S_Null
                          ) 
                          (S_Sequence 89
                            (S_If 90 (E_Binary_Operation 91 Greater_Than (E_Name 92 (E_Identifier 93 ((*T*) 9) ) ) (E_Literal 94 (Integer_Literal 1) (*nil*)) )
                              (S_Assignment 95 (E_Identifier 96 ((*T*) 9) ) (E_Binary_Operation 97 Plus (E_Name 98 (E_Identifier 99 ((*T*) 9) ) ) (E_Literal 100 (Integer_Literal 2) (*nil*)) ))
                              (S_Assignment 101 (E_Identifier 102 ((*T*) 9) ) (E_Binary_Operation 103 Minus (E_Name 104 (E_Identifier 105 ((*T*) 9) ) ) (E_Literal 106 (Integer_Literal 1) (*nil*)) ))
                            ) 
                            (S_Sequence 107
                              (S_While_Loop 108 (E_Binary_Operation 109 Greater_Than (E_Name 110 (E_Identifier 111 ((*T*) 9) ) ) (E_Literal 112 (Integer_Literal 0) (*nil*)) )
                                (S_Sequence 113
                                  (S_Assignment 114 (E_Identifier 115 ((*Result*) 8) ) (E_Binary_Operation 116 Divide (E_Binary_Operation 117 Multiply (E_Name 118 (E_Identifier 119 ((*Result*) 8) ) ) (E_Name 120 (E_Identifier 121 ((*T*) 9) ) ) ) (E_Name 122 (E_Identifier 123 ((*N*) 1) ) ) )) 
                                  (S_Assignment 124 (E_Identifier 125 ((*T*) 9) ) (E_Binary_Operation 126 Minus (E_Name 127 (E_Identifier 128 ((*T*) 9) ) ) (E_Literal 129 (Integer_Literal 1) (*nil*)) ))
                                )
                              ) 
                              (S_Assignment 130 (E_Identifier 131 ((*M*) 2) ) (E_Name 132 (E_Identifier 133 ((*Result*) 8) ) ))
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
