package body Simple_Arrays with SPARK_Mode
is
   pragma Warnings (Off, "* has no effect");

   type Enum_T is (Elem_0, Elem_1, Elem_2);

   type EnumI_EnumC is array (Enum_T)  of Enum_T;
   type IntI_EnumC  is array (Integer) of Enum_T;
   type EnumI_IntC  is array (Enum_T)  of Integer;
   type IntI_IntC   is array (Integer) of Integer;


   -- Array equality questions --

   procedure Array_Equality_Test (A, B : in IntI_IntC)
     with Depends => (null => (A, B))
   is
   begin
      pragma Assert ((A = B) =  --  @ASSERT:PASS
                       (for all I in Integer => A (I) = B (I)));
   end Array_Equality_Test;


   procedure Array_Equality_On_Bulk_Assignment (A : out IntI_IntC;
                                                B : in IntI_IntC)
     with Depends => (A => B),
          Post    => A = B  -- @POSTCONDITION:PASS
   is
   begin
      A := B;
   end Array_Equality_On_Bulk_Assignment;


   procedure Array_Equality_On_Individual_Assignment (A : out IntI_IntC;
                                                      B : IntI_IntC)
     with Depends => (A => B),
          Post    => A = B  -- @POSTCONDITION:PASS
   is
   begin
      for I in Integer loop
         A(I) := B(I);
         pragma Loop_Invariant
           (for all J in Integer range Integer'First .. I => A(J) = B(J));  -- @LOOP_INVARIANT_INIT:PASS @LOOP_INVARIANT_PRESERV:PASS
      end loop;
   end Array_Equality_On_Individual_Assignment;


   procedure Array_Equality_Information (A : in out IntI_IntC;
                                         B : out IntI_IntC;
                                         I : in Integer;
                                         V : in Integer)
      with Depends => ((A, B) => (A, I, V)),
           Post    => A = B  --  @POSTCONDITION:PASS
   is
   begin
      A(I) := V;
      B := A;
      B(I) := V;
   end Array_Equality_Information;


   procedure Array_Equality_Information_Obfuscated (A : in out IntI_IntC;
                                                    B : out IntI_IntC;
                                                    I1, I2 : in Integer;
                                                    V1, V2 : in Integer)
     with Depends => (A =>+ (I1, V1),
                      B => (A, I1, I2, V1, V2)),
          Post    => A /= B  --  @POSTCONDITION:FAIL
   is
   begin
      A(I1) := V1;
      B := A;
      B(I2) := V2;
   end Array_Equality_Information_Obfuscated;


   procedure Ordering_Matters (A : in out IntI_IntC;
                               N : in Integer)
     with Depends => (A =>+ N),
          Post    =>
            (if N /= 1 then A = (A'Old with delta 1 => 5,  --  @POSTCONDITION:PASS
                                              N => 6))
               and (if N /= 1 then A = (A'Old with delta N => 6,
                                                     1 => 5))
               and (if N /= 1 then A = (A with delta N => 6,
                                                 1 => 5))
   is
   begin
      pragma Assert ((A with delta 1 => 5,  --  @ASSERT:FAIL
                               N => 6) = (A with delta N => 6,
                                                   1 => 5));
      A(1) := 5;
      A(N) := 6;
   end Ordering_Matters;


   function Array_Axiom_Transitivity (A, B, C : in IntI_IntC) return Integer
     with Depends => (Array_Axiom_Transitivity'Result => C,
                      null => (A, B)),
          Pre     => A = B'Update (23 => 42) and A = C,
          Post    => Array_Axiom_Transitivity'Result = 42
   is
   begin
      return C(23);
   end Array_Axiom_Transitivity;


   function Array_Axiom_Transitivity_Worse (A, B, C, D : in IntI_IntC)
                                           return Integer
     with Depends => (Array_Axiom_Transitivity_Worse'Result => D,
                      null => (A, B, C)),
          Pre     => B = (A with delta 23 => 42)
                       and C = (A with delta 42 => 23,
                                         23 => 42)
                       and (D = B or D = C),
          Post    => Array_Axiom_Transitivity_Worse'Result = 42  --  @POSTCONDITION:PASS
   is
   begin
      return D(23);
   end Array_Axiom_Transitivity_Worse;


   procedure Update_Reordering (A : in out IntI_IntC;
                                I, J, K : Integer)
     with Depends => (A =>+ (I, J, K)),
          Pre     => I /= J and J /= K and K /= I,
          Post    => A = (A'Old with delta I => 1,  --  @POSTCONDITION:PASS
                                       J => 2,
                                       K => 3)
   is
   begin
      A(K) := 3;
      A(J) := 2;
      A(I) := 1;
   end Update_Reordering;


   procedure Update_Reordering_With_Help (A : in out IntI_IntC;
                                          I, J, K : Integer)
     with Depends => (A =>+ (I, J, K)),
          Pre     => I /= J and J /= K and K /= I,
          Post    => A = (A'Old with delta I => 1,  --  @POSTCONDITION:PASS
                                       J => 2,
                                       K => 3)
   is
      A_Old : constant IntI_IntC := A;
   begin
      A(K) := 3;
      A(J) := 2;
      A(I) := 1;

      pragma Assert ((A_Old with delta I => 1,  --  @ASSERT:PASS
                                   J => 2,
                                   K => 3) = (A_Old with delta I => 1,
                                                           K => 3,
                                                           J => 2));
      pragma Assert ((A_Old with delta I => 1,  --  @ASSERT:PASS
                                   K => 3,
                                   J => 2) = (A_Old with delta K => 3,
                                                           I => 1,
                                                           J => 2));
      pragma Assert ((A_Old with delta K => 3,  --  @ASSERT:PASS
                                   I => 1,
                                   J => 2) = (A_Old with delta K => 3,
                                                           J => 2,
                                                           I => 1));
   end Update_Reordering_With_Help;


   procedure Updates_And_Equality (A : in IntI_IntC;
                                   B, C : in out IntI_IntC;
                                   I, J : Integer)
     with Depends => (B =>+ J,
                      C =>+ I,
                      null => A),
          Pre     => B = (A with delta I => 23)
                       and C = (A with delta J => 42)
                       and I /= J,
          Post    => B = C  --  @POSTCONDITION:PASS
   is
   begin
      B(J) := 42;
      C(I) := 23;
   end Updates_And_Equality;


   procedure Update_Equality_Test_1 (A : in IntI_IntC;
                                     I : in Integer)
     with Depends => (null => (A, I))
   is
   begin
      pragma Assert ((A = (A with delta I => (42))) =  --  @ASSERT:PASS
                       (A (I) = 42));

      null;
   end Update_Equality_Test_1;


   procedure Update_Equality_Test_2 (A : in IntI_IntC;
                                     I : in Integer)
     with Depends => (null => (A, I))
   is
   begin
      pragma Assert ((A = (A with delta I => (42))) =  --  @ASSERT:PASS
                       (A (I) = IntI_IntC'(A with delta I => 42) (I)));

      null;
   end Update_Equality_Test_2;


   procedure Update_Equality_Test_3 (A, B : in IntI_IntC;
                                     I : in Integer)
     with Depends => (null => (A, B, I))
   is
   begin
      pragma Assert (if B = A then (B = (A with delta I => (42))) =
                       (A (I) = IntI_IntC'(A with delta I => 42) (I)));

      null;
   end Update_Equality_Test_3;


   procedure Update_Equality_Test_4 (A, B, C : in IntI_IntC;
                                     I : in Integer)
     with Depends => (null => (A, B, C, I))
   is
   begin
      pragma Assert
        (if (B = A and C = A) then (B = (C with delta I => 42)) =
                                      (A (I) = IntI_IntC'(A with delta I => 42) (I)));

      null;
   end Update_Equality_Test_4;


   procedure Update_Equality_Test_5 (A, B, C, D : in IntI_IntC;
                                     I : in Integer)
     with Depends => (null => (A, B, C, D, I))
   is
   begin
      pragma Assert (if (B = A
                           and C = A
                           and D = (C with delta I => 42))
                     then (B = D) = (A (I) = IntI_IntC'(A with delta I => 42) (I)));

      null;
   end Update_Equality_Test_5;


   procedure Update_Equality_Test_6 (A, B, C, D, E : in IntI_IntC;
                                     I : in Integer)
     with Depends => (null => (A, B, C, D, E, I))
   is
   begin
      pragma Assert (if (B = A
                           and C = A
                           and D = (C with delta I => 42)
                           and E = A)
                     then (B = D) = (E (I) = IntI_IntC'(A with delta I => 42) (I)));

      null;
   end Update_Equality_Test_6;


   procedure Update_Equality_Test_7 (A, B, C, D, E, F : in IntI_IntC;
                                     I : in Integer)
     with Depends => (null => (A, B, C, D, E, F, I))
   is
   begin
      pragma Assert (if (B = A
                           and C = A
                           and D = (C with delta I => 42)
                           and E = A
                           and F = A)
                     then (B = D) = (E (I) = IntI_IntC'(F with delta I => 42) (I)));

      null;
   end Update_Equality_Test_7;


   procedure Update_Equality_Test_8 (A, B, C, D, E, F, G : in IntI_IntC;
                                     I : in Integer)
     with Depends => (null => (A, B, C, D, E, F, G, I))
   is
   begin
      pragma Assert (if (B = A
                           and C = A
                           and D = (C with delta I => 42)
                           and E = A
                           and F = A
                           and G = (F with delta I => 42))
                     then (B = D) = (E (I) = G (I)));

      null;
   end Update_Equality_Test_8;


   procedure Update_Equality_Test_9 (A, B, C, D, E, F, G : in IntI_IntC;
                                     I, X : in Integer)
     with Depends => (null => (A, B, C, D, E, F, G, I, X))
   is
   begin
      pragma Assert (if (B = A
                           and C = A
                           and D = (C with delta I => 42)
                           and E = A
                           and F = A
                           and G = (F with delta I => 42)
                           and E (I) = X)
                     then (B = D) = (X = G (I)));

      null;
   end Update_Equality_Test_9;


   procedure Update_Equality_Test_10 (A, B, C, D, E, F, G : in IntI_IntC;
                                     I, X, Y : in Integer)
     with Depends => (null => (A, B, C, D, E, F, G, I, X, Y))
   is
   begin
      pragma Assert (if (B = A
                           and C = A
                           and D = (C with delta I => 42)
                           and E = A
                           and F = A
                           and G = (F with delta I => 42)
                           and E (I) = X
                           and G (I) = Y)
                     then ((B = D) = (X = Y)));

      null;
   end Update_Equality_Test_10;


   procedure Update_Equality_Test_11 (A, B, C, D, E, F, G : in IntI_IntC;
                                     I, J, X, Y : in Integer)
     with Depends => (null => (A, B, C, D, E, F, G, I, J, X, Y))
   is
   begin
      pragma Assert (if (B = A
                           and C = A
                           and D = (C with delta J => 42)
                           and E = A
                           and F = A
                           and G = (F with delta I => 42)
                           and E (I) = X
                           and G (J) = Y
                           and I = J)
                     then ((B = D) = (X = Y)));

      null;
   end Update_Equality_Test_11;


   procedure Update_Should_Behave_As_A_Symbolic_Function
     (A, B : in out IntI_IntC;
      I, J, X, Y : in Integer)
     with Depends => (A =>+ (I, X),
                      B =>+ (J, Y)),
          Post    => (if (A'Old = B'Old  --  @POSTCONDITION:PASS
                            and I = J
                            and X = Y)
                      then A = B)
   is
   begin
      A(I) := X;
      B(J) := Y;
   end Update_Should_Behave_As_A_Symbolic_Function;

   -- Array Axiom Tests --

   procedure Axiom_Test_1 (A : in IntI_IntC; I : in Integer; X : in Integer)
     with Depends => (null => (A, I, X))
   is
   begin
      pragma Assert (IntI_IntC'(A with delta I => X)(I) = X);  --  @ASSERT:PASS
      null;
   end Axiom_Test_1;


   procedure Axiom_Test_2 (A : in IntI_IntC; I : in Integer)
     with Depends => (null => (A, I))
   is
   begin
      pragma Assert (IntI_IntC'(A with delta I => A(I)) = A);  --  @ASSERT:PASS
      null;
   end Axiom_Test_2;


   procedure Axiom_Test_3 (A : in IntI_IntC; J, K : in Integer; X : in Integer)
     with Depends => (null => (A, J, K, X))
   is begin
      pragma Assert (if J /= K then  --  @ASSERT:PASS
                       IntI_IntC'(A with delta J => X) (K) = A (K));
      null;
   end Axiom_Test_3;


   -- Enum Index Enum Content tests --

   procedure EE_Constant_Access (A : in EnumI_EnumC)
   with Depends => (null => A)
   is
   begin
      pragma Assert (A(Elem_0) = Elem_0);  -- @ASSERT:FAIL
   end EE_Constant_Access;

   procedure EE_Variable_Access (A : in EnumI_EnumC; I : in Enum_T)
     with Depends => (null => (A, I))
   is
   begin
      pragma Assert (A(I) = Elem_0);  -- @ASSERT:FAIL
   end EE_Variable_Access;


   procedure EE_Constant_Update_And_Access (A : in out EnumI_EnumC)
     with Depends => (A => A),
          Post    => A(Elem_0) = Elem_0  --  @POSTCONDITION:FAIL
   is
   begin
      A(Elem_0) := Elem_1;
   end EE_Constant_Update_And_Access;


   procedure EE_Variable_Update_And_Access (A : in out EnumI_EnumC;
                                            I : in Enum_T)
     with Depends => (A =>+ I),
          Post    => A(I) = Elem_0  --  @POSTCONDITION:FAIL
   is
   begin
      A(I) := Elem_1;
   end EE_Variable_Update_And_Access;


   procedure EE_Constant_Overwrite (A : in out EnumI_EnumC)
     with Depends => (A => A),
          Post    => A(Elem_0) = Elem_1  --  @POSTCONDITION:FAIL
   is
   begin
      A(Elem_0) := Elem_1;
      A(Elem_0) := Elem_0;
   end EE_Constant_Overwrite;


   procedure EE_Variable_Overwrite (A : in out EnumI_EnumC; I : in Enum_T)
     with Depends => (A =>+ I),
          Post    => A(I) = Elem_1  --  @POSTCONDITION:FAIL
   is
   begin
      A(I) := Elem_1;
      A(I) := Elem_0;
   end EE_Variable_Overwrite;


   procedure EE_Constant_Passthrough (A : in out EnumI_EnumC)
     with Depends => (A => A),
          Post    => A(Elem_0) /= Elem_0  --  @POSTCONDITION:FAIL
   is
   begin
      A(Elem_0) := Elem_0;
      A(Elem_1) := Elem_1;
   end EE_Constant_Passthrough;


   procedure EE_Variable_Passthrough (A : in out EnumI_EnumC;
                                      I, J : in Enum_T)
     with Depends => (A =>+ (I, J)),
          Pre     => I /= J,
          Post    => A(I) /= Elem_0  --  @POSTCONDITION:FAIL
   is
   begin
      A(I) := Elem_0;
      A(J) := Elem_1;
   end EE_Variable_Passthrough;


   procedure EE_Constant_Swap (A : in out EnumI_EnumC)
     with Depends => (A => A),
          Post    => A /= A'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Enum_T;
   begin
      Tmp := A(Elem_0);
      A(Elem_0) := A(Elem_1);
      A(Elem_1) := Tmp;
   end EE_Constant_Swap;


   procedure EE_Variable_Swap (A : in out EnumI_EnumC;
                               I, J : in Enum_T)
     with Depends => (A =>+ (I, J)),
          Pre     => I /= J,
          Post    => A /= A'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Enum_T;
   begin
      Tmp  := A(I);
      A(I) := A(J);
      A(J) := Tmp;
   end EE_Variable_Swap;


   procedure EE_Constant_Two_Array_Swap (A, B : in out EnumI_EnumC)
     with Depends => ((A, B) => (A, B)),
          Post    => A /= A'Old and B /= B'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Enum_T;
   begin
      Tmp       := A(Elem_0);
      A(Elem_0) := B(Elem_1);
      B(Elem_1) := Tmp;
   end EE_Constant_Two_Array_Swap;


   procedure EE_Variable_Two_Array_Swap (A, B : in out EnumI_EnumC;
                                         I, J : in Enum_T)
     with Depends => ((A, B) => (A, B, I, J)),
          Post    => A /= A'Old and B /= B'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Enum_T;
   begin
      Tmp  := A(I);
      A(I) := B(J);
      B(J) := Tmp;
   end EE_Variable_Two_Array_Swap;



   -- Integer Index Enum Content tests --

   procedure IE_Constant_Access (A : in IntI_EnumC)
     with Depends => (null => A)
   is
   begin
      pragma Assert (A(42) = Elem_0);  --  @ASSERT:FAIL
   end IE_Constant_Access;


   procedure IE_Variable_Access (A : in IntI_EnumC; I : in Integer)
     with Depends => (null => (A, I))
   is
   begin
      pragma Assert (A(I) = Elem_0);  --  @ASSERT:FAIL
   end IE_Variable_Access;


   procedure IE_Constant_Update_And_Access (A : in out IntI_EnumC)
     with Depends => (A => A),
          Post    => A(42) = Elem_0  --  @POSTCONDITION:FAIL
   is
   begin
      A(42) := Elem_1;
   end IE_Constant_Update_And_Access;


   procedure IE_Variable_Update_And_Access (A : in out IntI_EnumC;
                                            I : in Integer)
     with Depends => (A =>+ I),
          Post    => A(I) = Elem_0  --  @POSTCONDITION:FAIL
   is
   begin
      A(I) := Elem_1;
   end IE_Variable_Update_And_Access;


   procedure IE_Constant_Overwrite (A : in out IntI_EnumC)
     with Depends => (A => A),
          Post    => A(42) = Elem_1  --  @POSTCONDITION:FAIL
   is
   begin
      A(42) := Elem_1;
      A(42) := Elem_0;
   end IE_Constant_Overwrite;


   procedure IE_Variable_Overwrite (A : in out IntI_EnumC; I : in Integer)
     with Depends => (A =>+ I),
          Post    => A(I) = Elem_1  --  @POSTCONDITION:FAIL
   is
   begin
      A(I) := Elem_1;
      A(I) := Elem_0;
   end IE_Variable_Overwrite;


   procedure IE_Constant_Passthrough (A : in out IntI_EnumC)
     with Depends => (A => A),
          Post    => A(42) /= Elem_0  --  @POSTCONDITION:FAIL
   is
   begin
      A(42) := Elem_0;
      A(23) := Elem_1;
   end IE_Constant_Passthrough;


   procedure IE_Variable_Passthrough (A : in out IntI_EnumC;
                                      I, J : in Integer)
     with Depends => (A =>+ (I, J)),
          Pre     => I /= J,
          Post    => A(I) /= Elem_0  --  @POSTCONDITION:FAIL
   is
   begin
      A(I) := Elem_0;
      A(J) := Elem_1;
   end IE_Variable_Passthrough;


   procedure IE_Constant_Swap (A : in out IntI_EnumC)
     with Depends => (A => A),
          Post    => A /= A'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Enum_T;
   begin
      Tmp   := A(42);
      A(42) := A(23);
      A(23) := Tmp;
   end IE_Constant_Swap;


   procedure IE_Variable_Swap (A : in out IntI_EnumC;
                               I, J : in Integer)
     with Depends => (A =>+ (I, J)),
          Pre     => I /= J,
          Post    => A /= A'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Enum_T;
   begin
      Tmp  := A(I);
      A(I) := A(J);
      A(J) := Tmp;
   end IE_Variable_Swap;


   procedure IE_Constant_Two_Array_Swap (A, B : in out IntI_EnumC)
     with Depends => ((A, B) => (A, B)),
          Post    => A /= A'Old and B /= B'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Enum_T;
   begin
      Tmp   := A(42);
      A(42) := B(23);
      B(23) := Tmp;
   end IE_Constant_Two_Array_Swap;


   procedure IE_Variable_Two_Array_Swap (A, B : in out IntI_EnumC;
                                         I, J : in Integer)
     with Depends => ((A, B) => (A, B, I, J)),
          Post    => A /= A'Old and B /= B'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Enum_T;
   begin
      Tmp  := A(I);
      A(I) := B(J);
      B(J) := Tmp;
   end IE_Variable_Two_Array_Swap;



   -- Enum Index Integer Content tests --

   procedure EI_Constant_Access (A : in EnumI_IntC)
     with Depends => (null => A)
   is
   begin
      pragma Assert (A(Elem_0) = 69);  --  @ASSERT:FAIL
   end EI_Constant_Access;


   procedure EI_Variable_Access (A : in EnumI_IntC; I : in Enum_T)
     with Depends => (null => (A, I))
   is
   begin
      pragma Assert (A(I) = 69);  --  @ASSERT:FAIL
   end EI_Variable_Access;


   procedure EI_Constant_Update_And_Access (A : in out EnumI_IntC)
     with Depends => (A => A),
          Post    => A(Elem_0) = 69  --  @POSTCONDITION:FAIL
   is
   begin
      A(Elem_0) := 1337;
   end EI_Constant_Update_And_Access;


   procedure EI_Variable_Update_And_Access (A : in out EnumI_IntC; I : in Enum_T)
     with Depends => (A =>+ I),
          Post    => A(I) = 69  --  @POSTCONDITION:FAIL
   is
   begin
      A(I) := 1337;
   end EI_Variable_Update_And_Access;


   procedure EI_Constant_Overwrite (A : in out EnumI_IntC)
     with Depends => (A =>+ null),
          Post    => A(Elem_0) = 1337  --  @POSTCONDITION:FAIL
   is
   begin
      A(Elem_0) := 1337;
      A(Elem_0) := 69;
   end EI_Constant_Overwrite;


   procedure EI_Variable_Overwrite (A : in out EnumI_IntC; I : in Enum_T)
     with Depends => (A =>+ I),
          Post    => A(I) = 1337  --  @POSTCONDITION:FAIL
   is
   begin
      A(I) := 1337;
      A(I) := 69;
   end EI_Variable_Overwrite;


   procedure EI_Constant_Passthrough (A : in out EnumI_IntC)
     with Depends => (A =>+ null),
          Post    => A(Elem_0) /= 69  --  @POSTCONDITION:FAIL
   is
   begin
      A(Elem_0) := 69;
      A(Elem_1) := 1337;
   end EI_Constant_Passthrough;


   procedure EI_Variable_Passthrough (A : in out EnumI_IntC;
                                      I, J : in Enum_T)
     with Depends => (A =>+ (I, J)),
          Pre     => I /= J,
          Post    => A(I) /= 69  --  @POSTCONDITION:FAIL
   is
   begin
      A(I) := 69;
      A(J) := 1337;
   end EI_Variable_Passthrough;


   procedure EI_Constant_Swap (A : in out EnumI_IntC)
     with Depends => (A =>+ null),
          Post    => A /= A'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Integer;
   begin
      Tmp       := A(Elem_0);
      A(Elem_0) := A(Elem_1);
      A(Elem_1) := Tmp;
   end EI_Constant_Swap;


   procedure EI_Variable_Swap (A : in out EnumI_IntC;
                               I, J : in Enum_T)
     with Depends => (A =>+ (I, J)),
          Pre     => I /= J,
          Post    => A /= A'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Integer;
   begin
      Tmp := A(I);
      A(I) := A(J);
      A(J) := Tmp;
   end EI_Variable_Swap;


   procedure EI_Constant_Two_Array_Swap (A, B : in out EnumI_IntC)
     with Depends => ((A, B) => (A, B)),
          Post    => A /= A'Old and B /= B'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Integer;
   begin
      Tmp := A(Elem_0);
      A(Elem_0) := B(Elem_1);
      B(Elem_1) := Tmp;
   end EI_Constant_Two_Array_Swap;


   procedure EI_Variable_Two_Array_Swap (A, B : in out EnumI_IntC;
                                         I, J : in Enum_T)
     with Depends => ((A, B) => (A, B, I, J)),
          Post    => A /= A'Old and B /= B'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Integer;
   begin
      Tmp := A(I);
      A(I) := B(J);
      B(J) := Tmp;
   end EI_Variable_Two_Array_Swap;



   -- Integer Index Integer Content tests --

   procedure II_Constant_Access (A : in IntI_IntC)
     with Depends => (null => A)
   is
   begin
      pragma Assert (A(42) = 69);  --  @ASSERT:FAIL
   end II_Constant_Access;


   procedure II_Variable_Access (A : in IntI_IntC; I : in Integer)
     with Depends => (null => (A, I))
   is
   begin
      pragma Assert (A(I) = 69);  --  @ASSERT:FAIL
   end II_Variable_Access;


   procedure II_Constant_Update_And_Access (A : in out IntI_IntC)
     with Depends => (A =>+ null),
          Post    => A(42) = 69  --  @POSTCONDITION:FAIL
   is
   begin
      A(42) := 1337;
   end II_Constant_Update_And_Access;


   procedure II_Variable_Update_And_Access (A : in out IntI_IntC;
                                            I : in Integer)
     with Depends => (A =>+ I),
          Post    => A(I) = 69  --  @POSTCONDITION:FAIL
   is
   begin
      A(I) := 1337;
   end II_Variable_Update_And_Access;


   procedure II_Constant_Overwrite (A : in out IntI_IntC)
     with Depends => (A =>+ null),
          Post    => A(42) = 1337  --  @POSTCONDITION:FAIL
   is
   begin
      A(42) := 1337;
      A(42) := 69;
   end II_Constant_Overwrite;


   procedure II_Variable_Overwrite (A : in out IntI_IntC; I : in Integer)
     with Depends => (A =>+ I),
          Post    => A(I) = 1337  --  @POSTCONDITION:FAIL
   is
   begin
      A(I) := 1337;
      A(I) := 69;
   end II_Variable_Overwrite;


   procedure II_Constant_Passthrough (A : in out IntI_IntC)
     with Depends => (A => A),
          Post    => A(42) /= 69  --  @POSTCONDITION:FAIL
   is
   begin
      A(42) := 69;
      A(23) := 1337;
   end II_Constant_Passthrough;


   procedure II_Variable_Passthrough (A : in out IntI_IntC;
                                      I, J : in Integer)
     with Depends => (A =>+ (I, J)),
          Pre     => I /= J,
          Post    => A(I) /= 69  --  @POSTCONDITION:FAIL
   is
   begin
      A(I) := 69;
      A(J) := 1337;
   end II_Variable_Passthrough;


   procedure II_Constant_Swap (A : in out IntI_IntC)
     with Depends => (A => A),
          Post    => A /= A'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Integer;
   begin
      Tmp   := A(42);
      A(42) := A(23);
      A(23) := Tmp;
   end II_Constant_Swap;


   procedure II_Variable_Swap (A : in out IntI_IntC;
                               I, J : in Integer)
     with Depends => (A =>+ (I, J)),
          Pre     => I /= J,
          Post    => A /= A'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Integer;
   begin
      Tmp  := A(I);
      A(I) := A(J);
      A(J) := Tmp;
   end II_Variable_Swap;


   procedure II_Constant_Two_Array_Swap (A, B : in out IntI_IntC)
     with Depends => ((A, B) => (A, B)),
          Post    => A /= A'Old and B /= B'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Integer;
   begin
      Tmp   := A(42);
      A(42) := B(23);
      B(23) := Tmp;
   end II_Constant_Two_Array_Swap;


   procedure II_Variable_Two_Array_Swap (A, B : in out IntI_IntC;
                                         I, J : in Integer)
     with Depends => ((A, B) => (A, B, I, J)),
          Post    => A /= A'Old and B /= B'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Integer;
   begin
      Tmp  := A(I);
      A(I) := B(J);
      B(J) := Tmp;
   end II_Variable_Two_Array_Swap;

   pragma Warnings (On, "* has no effect");
end Simple_Arrays;
