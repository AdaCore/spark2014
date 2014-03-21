package body Basic
is
   type Unsigned_Byte is range 0 .. 255;

   function Add_UB (A, B: Unsigned_Byte) return Unsigned_Byte
     with Post => Add_UB'Result = A + B
   is
   begin
      return A + B;  --  @RANGE_CHECK:FAIL
   end Add_UB;

   function Add_I (A, B: Integer) return Integer
     with Post => Add_I'Result = A + B
   is
   begin
      return A + B;  --  @OVERFLOW_CHECK:FAIL
   end Add_I;

   function Min_UB (A, B: Unsigned_Byte) return Unsigned_Byte
     with Post => (Min_UB'Result <= A
                     and then Min_UB'Result <= B
                     and then (Min_UB'Result = A or else Min_UB'Result = B))
   is
      R : Unsigned_Byte;
   begin
      if A <= B then
         R := A;
      else
         R := B;
      end if;
      pragma Assert_And_Cut ((if A <= B then R = A)
        and then (if B <= A then R = B));
      return R;
   end Min_UB;

   pragma Warnings (Off, "* has no effect");
   procedure Plus_Test
   is
   begin
      pragma Assert (5 = 2 + 3);
      pragma Assert_And_Cut (True);
      pragma Assert (5 = 1 + 1 + 1 + 1 + 1);
      pragma Assert_And_Cut (True);
      null;
   end Plus_Test;
   pragma Warnings (On, "* has no effect");

   procedure Tilde_Test_A (X : in out Integer)
     with Depends => (X => X),
          Pre     => X > 0 and then X < 10,
          Post    => X = X'Old + 5
   is
      X_Old : constant Integer := X;
   begin
      X := X + 3;
      pragma Assert_And_Cut (X >= X_Old + 3
                               and then X <= X_Old + 3);
      X := X + 2;
   end Tilde_Test_A;

   procedure Tilde_Test_B (X : in out Integer)
     with Depends => (X => X),
          Pre     => X > 0 and then X < 10,
          Post    => X = X'Old + 5  --  @POSTCONDITION:FAIL
   is
      X_Old : constant Integer := X;
   begin
      X := X + 3;
      pragma Assert_And_Cut (X >= X_Old + 3
                               and then X <= X_Old + 3);
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
     with Post => Int_Min_B'Result = Integer'Min (A, B) --  @POSTCONDITION:FAIL
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
                      null => Y),
          Pre     => X = Y,
          Post    => Equality_Rewrite_Loop_Test'Result = Y
   is
   begin
      pragma Assert (X = X);
      pragma Assert (Y = X);
      return X;
   end Equality_Rewrite_Loop_Test;

   --  This is a testcase for L813-012 showing that SPARK/FDL
   --  variables can potentially namecapture AnsPL variables (or
   --  constants in this case).
   --
   --  To fix this we need to name-mangle all user-inputs.
   procedure Be_Aware_Of_Name_Capture_In_AnsPL (Bi_Const_0 : out Integer)
     with Post => Bi_Const_0 = 5  --  @POSTCONDITION:FAIL
   is
   begin
      Bi_Const_0 := 3;
      pragma Assert_And_Cut (Bi_Const_0 in 0..10);
   end Be_Aware_Of_Name_Capture_In_AnsPL;
end Basic;
