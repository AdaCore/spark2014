package body Records
is
   pragma Warnings (Off, "* has no effect");

   function Init_A return Pair
     with Post => Init_A'Result = Pair' (A => 0, B => 0)  --  @POSTCONDITION:PASS
   is
      R : Pair;
   begin
      R := Pair'(A => 0,
                 B => 0);
      return R;
   end Init_A;

   function Init_B return Pair
     with Post => (Init_B'Result.A = 0 and Init_B'Result.B < 1)  --  @POSTCONDITION:PASS
   is
      R : Pair;
   begin
      R := Pair'(A => 0,
                 B => 0);
      return R;
   end Init_B;

   function Init_C return Pair
     with Post => Init_C'Result = Null_Pair  --  @POSTCONDITION:PASS
   is
      R : Pair;
   begin
      R := Pair'(A => 0,
                 B => 0);
      return R;
   end Init_C;

   function Init_D return Pair
     with Post => Init_D'Result = Null_Pair  --  @POSTCONDITION:PASS
   is
      R : Pair;
   begin
      R := Null_Pair;
      return R;
   end Init_D;

   function Init_E return Optional_Pair
     with Post => Init_E'Result = Null_Optional_Pair  --  @POSTCONDITION:PASS
   is
   begin
      return Optional_Pair'(Exists   => False,
                            The_Pair => Pair'(A => 0,
                                              B => 0));
   end Init_E;

   function Add_Pair_A (A, B : in Pair) return Pair
     with Pre  => A.A + B.A in Unsigned_Byte
                    and A.B + B.B in Unsigned_Byte,
          Post => Add_Pair_A'Result = Pair'(A => A.A + B.A,  --  @POSTCONDITION:PASS
                                            B => A.B + B.B)
   is
   begin
      return Pair'(A => A.A + B.A,
                   B => A.B + B.B);
   end Add_Pair_A;

   function Safe_Add_Pair_A (A, B : in Pair) return Pair
     with Post => (if (A.A + B.A in Unsigned_Byte and  --  @POSTCONDITION:PASS
                         A.B + B.B in Unsigned_Byte)
                   then Safe_Add_Pair_A'Result = Pair'(A.A + B.A,
                                                       A.B + B.B))
   is
      R : Pair;
   begin
      if A.A <= Unsigned_Byte'Last - B.A and then
        A.B <= Unsigned_Byte'Last - B.B
      then
         R := Add_Pair_A (A, B);
      else
         R := Pair'(A => 0,
                    B => 0);
      end if;
      return R;
   end Safe_Add_Pair_A;

   function Safe_Add_Pair_B (A, B : in Pair) return Pair
     with Post => (if (A.A + B.A in Unsigned_Byte and
                         A.B + B.B in Unsigned_Byte)
                   then Safe_Add_Pair_B'Result = Pair'(A.A + B.A,  --  @POSTCONDITION:FAIL @COUNTEREXAMPLE
                                                       A.B + B.B))
   is
      R : Pair;
   begin
      if A.A + 1 <= Unsigned_Byte'Last - B.A and then
        A.B <= Unsigned_Byte'Last - B.B
      then
         R := Add_Pair_A (A, B);
      else
         R := Pair'(A => 0,
                    B => 0);
      end if;
      return R;
   end Safe_Add_Pair_B;

   function Is_Valid (A : in Optional_Pair) return Boolean
     with Post => Is_Valid'Result = (if not A.Exists  --  @POSTCONDITION:PASS
                                       then A.The_Pair = Null_Pair)
   is
   begin
      return A.Exists or else A.The_Pair = Null_Pair;
   end Is_Valid;

   function Is_Valid_B (A : in Optional_Pair) return Boolean
     with Post => Is_Valid_B'Result = (if not A.Exists  --  @POSTCONDITION:PASS
                                         then A.The_Pair = Null_Pair)
   is
   begin
      return A.Exists or else A.The_Pair = Pair'(A => 0, B => 0);
   end Is_Valid_B;

   function Is_Valid_C (A : in Optional_Pair) return Boolean
     with Post => Is_Valid_C'Result = (if not A.Exists  --  @POSTCONDITION:FAIL @COUNTEREXAMPLE
                                         then A.The_Pair = Null_Pair)
   is
   begin
      return A.Exists
        or else A.The_Pair = Pair'(A => 1,
                                   B => 0);
   end Is_Valid_C;

   procedure Copy_OP_A (Src : in     Optional_Pair;
                        Dst :    out Optional_Pair)
     with Depends => (Dst => Src),
          Pre     => Is_Valid (Src),
          Post    => Is_Valid (Dst) and Dst = Src  --  @POSTCONDITION:PASS
   is
   begin
      Dst := Src;
   end Copy_Op_A;

   procedure Copy_OP_B (Src : in     Optional_Pair;
                        Dst :    out Optional_Pair)
     with Depends => (Dst => Src),
          Pre     => Is_Valid (Src),
          Post    => Is_Valid (Dst) and Dst = Src  --  @POSTCONDITION:FAIL @COUNTEREXAMPLE
   is
   begin
      Dst := Src;
      Dst.Exists := False;
   end Copy_Op_B;

   procedure Optimised_Copy_A (Src : in     Optional_Pair;
                               Dst :    out Optional_Pair)
     with Depends => (Dst => Src),
          Post    => (Src.Exists = Dst.Exists)  --  @POSTCONDITION:PASS
                        and (if Src.Exists then Dst = Src)
   is
      pragma Annotate (Gnatprove, False_Positive, "might not be initialized", "");
   begin
      Dst.Exists := Src.Exists;
      if Src.Exists then
         Dst.The_Pair := Src.The_Pair;
      end if;
   end Optimised_Copy_A;

   procedure Optimised_Copy_B (Src : in     Optional_Pair;
                               Dst :    out Optional_Pair)
     with Depends => (Dst => Src),
          Post    => Dst = Src  --  @POSTCONDITION:FAIL @COUNTEREXAMPLE
   is
      pragma Annotate (Gnatprove, False_Positive, "might not be initialized", "");
   begin
      Dst.Exists := Src.Exists;
      if Src.Exists then
         Dst.The_Pair := Src.The_Pair;
      end if;
   end Optimised_Copy_B;

   procedure Swap_Fields_A_1 (X : in out Optional_Pair)
     with Depends => (X =>+ null),
          Post    => (X.Exists = X'Old.Exists)  --  @POSTCONDITION:PASS
                       and (if X.Exists
                              then (X.The_Pair.A = X'Old.The_Pair.B
                                      and X.The_Pair.B = X'Old.The_Pair.A))
   is
      Tmp : Unsigned_Byte;
   begin
      Tmp          := X.The_Pair.A;
      X.The_Pair.A := X.The_Pair.B;
      X.The_Pair.B := Tmp;
   end Swap_Fields_A_1;

   procedure Swap_Fields_A_2 (X : in out Optional_Pair)
     with Depends => (X =>+ null),
          Post    => (X.Exists = X'Old.Exists)
                       and (if X.Exists
                              then (X.The_Pair.A = X'Old.The_Pair.B
                                      and X.The_Pair.B = X'Old.The_Pair.A))  --  @POSTCONDITION:FAIL @COUNTEREXAMPLE
   is
      Tmp : Unsigned_Byte;
   begin
      Tmp          := X.The_Pair.B;
      X.The_Pair.A := X.The_Pair.B;
      X.The_Pair.B := Tmp;
   end Swap_Fields_A_2;

   procedure Swap_Fields_A_2_Cut (X : in out Optional_Pair)
     with Depends => (X =>+ null),
          Post    => (X.Exists = X'Old.Exists)
                        and (if X.Exists
                               then (X.The_Pair.A = X'Old.The_Pair.B
                                       and X.The_Pair.B = X'Old.The_Pair.A))  --  @POSTCONDITION:FAIL @COUNTEREXAMPLE
   is
      Tmp   : Unsigned_Byte;
      X_Old : constant Optional_Pair := X;
   begin
      Tmp          := X.The_Pair.B;
      pragma Assert_And_Cut (X = X_Old  --  @ASSERT:PASS
                               and Tmp = X.The_Pair.B);
      X.The_Pair.A := X.The_Pair.B;
      pragma Assert_And_Cut
        (X = X_Old'Update (The_Pair =>  --  @ASSERT:PASS
                             X_Old.The_Pair'Update(A => X_Old.The_Pair.B))
           and Tmp = X_Old.The_Pair.B);
      X.The_Pair.B := Tmp;
   end Swap_Fields_A_2_Cut;

   procedure Swap_Fields_A_3 (X : in out Optional_Pair)
     with Depends => (X =>+ null),
          Post    => (X.Exists = X'Old.Exists)  --  @POSTCONDITION:PASS
                       and (if X.Exists
                              then (X.The_Pair.A = X'Old.The_Pair.B
                                      and X.The_Pair.B = X'Old.The_Pair.A))
   is
      Tmp : Unsigned_Byte;
   begin
      if X.Exists then
         Tmp          := X.The_Pair.A;
         X.The_Pair.A := X.The_Pair.B;
         X.The_Pair.B := Tmp;
      end if;
   end Swap_Fields_A_3;

   procedure Swap_Fields_B_1 (X : in out Optional_Pair)
     with Depends => (X =>+ null),
          Post    => X = X'Old'Update (The_Pair =>  --  @POSTCONDITION:PASS
                                         (A => X'Old.The_Pair.B,
                                          B => X'Old.The_Pair.A))
   is
      Tmp : Unsigned_Byte;
   begin
      Tmp          := X.The_Pair.A;
      X.The_Pair.A := X.The_Pair.B;
      X.The_Pair.B := Tmp;
   end Swap_Fields_B_1;

   procedure Swap_Fields_B_2 (X : in out Optional_Pair)
     with Depends => (X =>+ null),
          Post    => X = X'Old'Update (The_Pair =>  --  @POSTCONDITION:FAIL @COUNTEREXAMPLE
                                         X'Old.The_Pair'Update
                                           (A => X'Old.The_Pair.B,
                                            B => X'Old.The_Pair.A))
   is
      Tmp : Unsigned_Byte;
   begin
      Tmp          := X.The_Pair.B;
      X.The_Pair.A := X.The_Pair.B;
      X.The_Pair.B := Tmp;
   end Swap_Fields_B_2;

   procedure Swap_Fields_B_3 (X : in out Optional_Pair)
     with Depends => (X =>+ null),
          Post    => X = X'Old'Update (The_Pair =>  --  @POSTCONDITION:FAIL @COUNTEREXAMPLE
                                         X'Old.The_Pair'Update
                                           (A => X'Old.The_Pair.B,
                                            B => X'Old.The_Pair.A))
   is
      Tmp : Unsigned_Byte;
   begin
      if X.Exists then
         Tmp          := X.The_Pair.A;
         X.The_Pair.A := X.The_Pair.B;
         X.The_Pair.B := Tmp;
      end if;
   end Swap_Fields_B_3;

   procedure Swap_Fields_C (X : in out Optional_Pair)
     with Depends => (X =>+ null),
          Post    => (X.Exists = X'Old.Exists)  --  @POSTCONDITION:PASS
                        and (if X.Exists
                               then (X.The_Pair.A = X'Old.The_Pair.B
                                       and X.The_Pair.B = X'Old.The_Pair.A))
   is
   begin
      X.The_Pair := Pair'(X.The_Pair.B, X.The_Pair.A);
   end Swap_Fields_C;

   procedure Swap_Fields_D (X : in out Optional_Pair)
     with Depends => (X =>+ null),
          Post    => (X.Exists = X'Old.Exists)
                        and (if X.Exists
                               then (X.The_Pair.A = X'Old.The_Pair.B
                                       and X.The_Pair.B = X'Old.The_Pair.A))  --  @POSTCONDITION:FAIL @COUNTEREXAMPLE
   is
   begin
      X.The_Pair := Pair'(X.The_Pair.B, 5);
   end Swap_Fields_D;

   function Update_A (X: in Optional_Pair;
                      N: in Unsigned_Byte)
                     return Optional_Pair
     with Post => Update_A'Result = X'Update(The_Pair =>  --  @POSTCONDITION:PASS
                                               X.The_Pair'Update (A => N))
   is
      Tmp : Optional_Pair;
   begin
      Tmp := X;
      Tmp.The_Pair.A := N;
      return Tmp;
   end Update_A;

   function Update_B (X: in Optional_Pair;
                      N: in Unsigned_Byte)
                     return Optional_Pair
     with Pre  => N < Unsigned_Byte'Last,
          Post => Update_B'Result = X'Update(The_Pair =>  --  @POSTCONDITION:FAIL @COUNTEREXAMPLE
                                               X.The_Pair'Update (A => N))
   is
      Tmp : Optional_Pair;
   begin
      Tmp := X;
      Tmp.The_Pair.A := N + 1;
      return Tmp;
   end Update_B;

   procedure Test_A (X: in out Optional_Pair)
     with Depends => (X =>+ null),
          Post    => X = X'Old'Update (The_Pair =>  --  @POSTCONDITION:PASS
                                         X'Old.The_Pair'Update
                                           (A => X'Old.The_Pair.B))
   is
   begin
      X := Update_A (X, X.The_Pair.B);
   end Test_A;

   procedure Test_B (X: in out Optional_Pair)
     with Depends => (X =>+ null),
          Post    => X.The_Pair.A = X'Old.The_Pair.B  --  @POSTCONDITION:PASS
   is
   begin
      X := Update_A (X, X.The_Pair.B);
   end Test_B;

   function Is_Null_A (X: in Optional_Pair) return Boolean
     with Post => Is_Null_A'Result = (X = Null_Optional_Pair)  --  @POSTCONDITION:PASS
   is
   begin
      return X = Null_Optional_Pair;
   end Is_Null_A;

   function Is_Null_B (X: in Optional_Pair) return Boolean
     with Post => Is_Null_B'Result = (X = Null_Optional_Pair)  --  @POSTCONDITION:PASS
   is
   begin
      return not X.Exists and X.The_Pair = Null_Pair;
   end Is_Null_B;

   function Make_Optional_Pair_A_1 (X: in Pair) return Optional_Pair
     with Post => Make_Optional_Pair_A_1'Result =  --  @POSTCONDITION:PASS
                    Optional_Pair' (Exists   => True,
                                    The_Pair => X)
   is
      R : Optional_Pair;
   begin
      R := Optional_Pair'(Exists   => True,
                          The_Pair => Pair'(A => 0,
                                            B => 0));
      R.The_Pair := X;
      return R;
   end Make_Optional_Pair_A_1;

   function Make_Optional_Pair_A_2 (X: in Pair) return Optional_Pair
     with Post => Make_Optional_Pair_A_2'Result =  --  @POSTCONDITION:FAIL @COUNTEREXAMPLE
                    Optional_Pair'(Exists   => False,
                                   The_Pair => X)
   is
      R : Optional_Pair;
   begin
      R := Optional_Pair'(Exists   => True,
                          The_Pair => Pair'(A => 0,
                                            B => 0));
      R.The_Pair := X;
      return R;
   end Make_Optional_Pair_A_2;

   function Make_Optional_Pair_B (X: in Pair) return Optional_Pair
     with Post => Make_Optional_Pair_B'Result =  --  @POSTCONDITION:PASS
                    Optional_Pair'(Exists   => True,
                                   The_Pair => X)
   is
      R : Optional_Pair;
   begin
      R := Optional_Pair'(Exists   => True,
                          The_Pair => X);
      return R;
   end Make_Optional_Pair_B;

   procedure Test_C (X: in out Optional_Pair)
     with Depends => (X =>+ null)
   is
   begin
      X := X;
      pragma Assert (X.The_Pair.A = 0);  --  @ASSERT:FAIL @COUNTEREXAMPLE
   end Test_C;

   procedure Test_D (X: in out Optional_Pair)
     with Depends => (X =>+ null)
   is
   begin
      X := X;
      pragma Assert (X.The_Pair.A = X.The_Pair.B);  --  @ASSERT:FAIL @COUNTEREXAMPLE
   end Test_D;

   procedure Test_E (X: in out Optional_Pair)
     with Depends => (X =>+ null)
   is
   begin
      X.The_Pair.A := X.The_Pair.B;
      pragma Assert (X.The_Pair.A /= X.The_Pair.B);  --  @ASSERT:FAIL
   end Test_E;

   procedure Test_F (X: out Optional_Pair)
     with Depends => (X => null)
   is
   begin
      X := Optional_Pair'(Exists   => True,
                          The_Pair => Pair'(A => 5,
                                            B => 10));
      pragma Assert (not X.Exists);  --  @ASSERT:FAIL @COUNTEREXAMPLE
   end Test_F;

   function Swap_Fields (P: in Pair) return Pair
   is
   begin
      return Pair'(A => P.B,
                   B => P.A);
   end Swap_Fields;

   function Apply_Command (P : in Packet) return Pair
   is
      R : Pair;
   begin
      case P.Command is
         when Increment_A =>
            R   := P.Data;
            R.A := R.A + 1;  --  @RANGE_CHECK:FAIL @COUNTEREXAMPLE
         when Assign_A =>
            R := Pair'(A => P.Data.B,
                       B => P.Data.B);
         when Swap =>
            R := Swap_Fields (P.Data);
      end case;
      return R;
   end Apply_Command;

   procedure Tilde_Test_A (R: in out Optional_Pair;
                           X: in     Unsigned_Byte)
     with Depends => (R =>+ X),
          Post    => R = R'Old'Update (The_Pair =>  --  @POSTCONDITION:PASS
                                         R'Old.The_Pair'Update
                                           (A => X,
                                            B => X))
   is
      R_Old : constant Optional_Pair := R;
   begin
      R.The_Pair.A := X;
      pragma Assert_And_Cut (R = R_Old'Update (The_Pair =>  --  @ASSERT:PASS
                                                 R_Old.The_Pair'Update
                                                   (A => X)));
      R.The_Pair.B := X;
   end Tilde_Test_A;

   procedure Tilde_Test_B (R: in out Optional_Pair;
                           X: in     Unsigned_Byte)
     with Depends => (R =>+ X),
          Post    => R = R'Old'Update (The_Pair =>  --  @POSTCONDITION:FAIL @COUNTEREXAMPLE
                                         R'Old.The_Pair'Update
                                           (A => X,
                                            B => X))
   is
      R_Old : constant Optional_Pair := R;
   begin
      R.The_Pair.A := X;
      pragma Assert_And_Cut (R = R_Old'Update (The_Pair =>  --  @ASSERT:PASS
                                                 R_Old.The_Pair'Update
                                                   (A => X)));
      R.The_Pair.B := 0;
   end Tilde_Test_B;


   function Field_Suppression_On_Computation_Is_Insufficient
     (R : in Optional_Pair)
     return Boolean
     with Post => Field_Suppression_On_Computation_Is_Insufficient'Result = True  --  @POSTCONDITION:PASS
   is
   begin
      pragma Assert (R.Exists);  --  @ASSERT:FAIL

      return R.Exists;
   end Field_Suppression_On_Computation_Is_Insufficient;


   procedure Update_Should_Behave_As_A_Symbolic_Function
     (R1 : in out Part_Private;
      R2 : in Part_Private)
     with Depends => (R1 =>+ R2),
          Post    => (if R1.Hidden = R2.Hidden then R1 = R2)  --  @POSTCONDITION:PASS
   is
   begin
      R1.Unrelated := R2.Unrelated;
   end Update_Should_Behave_As_A_Symbolic_Function;

   function Test_Record_Subtype (R1 : in Packet;
                                 R2 : in Record_Subtype)
                                return Boolean
     with Post => Test_Record_Subtype'Result = (R1 = R2)  --  @POSTCONDITION:PASS
   is
   begin
      return R1.Data = R2.Data and R1.Command = R2.Command;
   end Test_Record_Subtype;

   procedure Aggregate_In_Quantifier
     with Depends => null,
          Pre     => (for all N in Unsigned_Byte => F_Of_Pair (Pair'(0, N)))
   is
   begin
      pragma Assert (F_Of_Pair (Pair'(5, 5)));  --  @ASSERT:FAIL
      null;
   end Aggregate_In_Quantifier;

   pragma Warnings (On, "* has no effect");
end Records;
