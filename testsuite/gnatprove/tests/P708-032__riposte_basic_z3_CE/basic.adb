package body Basic
is
   type Unsigned_Byte is range 0 .. 255;

   function Add_UB (A, B: Unsigned_Byte) return Unsigned_Byte
     with Post => Add_UB'Result = A + B
   is
   begin
      return A + B;  --  @RANGE_CHECK:FAIL @COUNTEREXAMPLE
   end Add_UB;

   function Add_I (A, B: Integer) return Integer
     with Post => Add_I'Result = A + B
   is
   begin
      return A + B;  --  @OVERFLOW_CHECK:FAIL @COUNTEREXAMPLE
   end Add_I;

   function Min_UB (A, B: Unsigned_Byte) return Unsigned_Byte
     with Post => (Min_UB'Result <= A and
                   Min_UB'Result <= B and
                   (Min_UB'Result = A or Min_UB'Result = B))
   is
      R : Unsigned_Byte;
   begin
      if A <= B then
         R := A;
      else
         R := B;
      end if;
      pragma Assert_And_Cut ((if A <= B then R = A) and
                             (if B <= A then R = B));
      return R;
   end Min_UB;

   --  FS: Rewritten from original test as the front-end constant
   --      folds everything to true otherwise.
   procedure Plus_Test (One, Two, Three : Integer;
                        X, Y            : out Integer)
   with Pre  => One = 1 and Two = 2 and Three = 3,
        Post => X = 5 and Y = 5
   is
   begin
      X := Two + Three;
      Y := One + One + One + One + One;
   end Plus_Test;

   --  FS: This test was originally for the SPARK 2005 x~ notation,
   --  but 'Old in SPARK 2014 does not quite work the same way.
   procedure Tilde_Test_A (X : in out Integer)
     with Depends => (X => X),
          Pre     => X > 0 and X < 10,
          Post    => X = X'Old + 5
   is
      X_Old : constant Integer := X;
   begin
      X := X + 3;
      pragma Assert_And_Cut (X >= X_Old + 3 and X <= X_Old + 3);
      X := X + 2;
   end Tilde_Test_A;

   procedure Tilde_Test_B (X : in out Integer)
     with Depends => (X => X),
          Pre     => X > 0 and X < 10,
          Post    => X = X'Old + 5  --  @POSTCONDITION:FAIL @COUNTEREXAMPLE
   is
      X_Old : constant Integer := X;
   begin
      X := X + 3;
      pragma Assert_And_Cut (X >= X_Old + 3 and X <= X_Old + 3);
      X := X + 3;
   end Tilde_Test_B;

   function Int_Min_A (A, B : in Integer) return Integer
     with Post => Int_Min_A'Result = Integer'Min (A, B)
   is
      R : Integer;
   begin
      if A < B then
         R := A;
      else
         R := B;
      end if;
      return R;
   end Int_Min_A;

   function Int_Min_B (A, B : in Integer) return Integer
     with Post => Int_Min_B'Result = Integer'Min (A, B) --  @POSTCONDITION:FAIL @COUNTEREXAMPLE
   is
      R : Integer;
   begin
      if A < 0 then
         R := A;
      else
         R := B;
      end if;
      return R;
   end Int_Min_B;

   function Int_Max_A (A, B : in Integer) return Integer
     with Post => Int_Max_A'Result = Integer'Max (A, B)
   is
      R : Integer;
   begin
      if A > B then
         R := A;
      else
         R := B;
      end if;
      return R;
   end Int_Max_A;

   function Equality_Rewrite_Loop_Test (X, Y : in Integer) return Integer
     with Depends => (Equality_Rewrite_Loop_Test'Result => X,
                      null                              => Y),
          Pre     => X = Y,
          Post    => Equality_Rewrite_Loop_Test'Result = Y
   is
   begin
      pragma Assert (X = X);  --  FS: Rewritten by front-end, see N321-020
      pragma Assert (Y = X);
      return X;
   end Equality_Rewrite_Loop_Test;

end Basic;
