with Ada.Numerics.Big_Numbers.Big_Reals;
with Ada.Numerics.Big_Numbers.Big_Integers;
with Real_Convs; use Real_Convs;

procedure Big_Reals_Test with SPARK_Mode is

   package BR renames Ada.Numerics.Big_Numbers.Big_Reals; use BR;
   package MFC renames My_Float_Conversions; use MFC;
   package MIC renames My_Fixed_Conversions; use MIC;

   procedure Divide_Division_Check_Fail (R : Big_Real) is
      use Ada.Numerics.Big_Numbers.Big_Integers;
      C : Big_Integer := To_Big_Integer (0);
      D : Big_Real;
   begin
      pragma Assert (To_Big_Real (C) = To_Real (0));
      D := R / To_Big_Real (C); --  @DIVISION_CHECK:FAIL
   end Divide_Division_Check_Fail;

   procedure Check_Conv with Pre => True is
      Fl : Float := 0.5;
      Fi : My_Fixed := 0.5;
      D  : Big_Real;
   begin
      --  Conversions
      D := To_Big_Real (Fl);
      pragma Assert (D * To_Real (2) = To_Real (1));
      D := To_Big_Real (Fi);
      pragma Assert (D * To_Real (2) = To_Real (1));
   end Check_Conv;

   A, B, C, D : Big_Real;
begin
   A := To_Real (5);
   B := To_Real (5);
   C := To_Real (4);
   D := To_Real (9);

   --  Comparisons
   pragma Assert (A = B);
   pragma Assert (not (A = C));
   pragma Assert (A < D);
   pragma Assert (C < A);
   pragma Assert (not (A < B));
   pragma Assert (A <= B);
   pragma Assert (C <= A);
   pragma Assert (not (D <= A));
   pragma Assert (D > B);
   pragma Assert (B > C);
   pragma Assert (not (A > D));
   pragma Assert (not (B > B));
   pragma Assert (D >= A);
   pragma Assert (A >= C);
   pragma Assert (not (A > D));
   pragma Assert (B >= B);
   pragma Assert (In_Range (A, C, D));

   if Is_Valid (A) then
      null;
   end if;

   --  Operators
   A := To_Real (5);
   B := To_Real (-5);
   pragma Assert (A + C = D);
   pragma Assert (D - A = C);
   pragma Assert (+B = B);
   pragma Assert (-A = B);
   pragma Assert (abs B = A);
   pragma Assert (A * B = -A * A);
   pragma Assert (B ** 2 = A ** 2);
   pragma Assert (A / B = To_Real (-1));

   --  Functions
   pragma Assert (Min (A, B) = B);
   pragma Assert (Max (B, A) = A);

   Check_Conv;

   --  Smoke detector
   pragma Assert (In_Range (A, D, C)); --  @ASSERT:FAIL
end Big_Reals_Test;
