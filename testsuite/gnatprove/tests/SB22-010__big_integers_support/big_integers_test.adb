with Ada.Numerics.Big_Numbers.Big_Integers;
with Interfaces.C; use Interfaces.C;
with Types; use Types;
with Curve25519; use Curve25519;

procedure Big_Integers_Test with SPARK_Mode is

   package BI renames Ada.Numerics.Big_Numbers.Big_Integers; use BI;

   package My_Signed_Conversions is new
     Signed_Conversions (Int => Long_Long_Integer);
   package MSC renames My_Signed_Conversions; use MSC;

   package My_Unsigned_Conversions is new
     Unsigned_Conversions (Int => Unsigned);
   package MUC renames My_Unsigned_Conversions; use MUC;

   procedure Nat_Predicate_Check_Fail (Nat : out Big_Natural) is
   begin
      Nat := BI.To_Big_Integer (-1); --  @PREDICATE_CHECK:FAIL
      Nat := BI.To_Big_Integer (1);
   end Nat_Predicate_Check_Fail;

   procedure Pos_Predicate_Check_Fail (Pos : out Big_Positive) is
   begin
      Pos := BI.To_Big_Integer (0); --  @PREDICATE_CHECK:FAIL
      Pos := BI.To_Big_Integer (1);
   end Pos_Predicate_Check_Fail;

   procedure BI_Range_Check_Fail  (Big_Int : out Big_Integer; Int : out Integer)is
   begin
      Big_Int := BI.To_Big_Integer (Integer'Last);
      Big_Int := Big_Int + BI.To_Big_Integer (1);
      Int := To_Integer (Big_Int); --  @RANGE_CHECK:FAIL
      Int := 0;
   end BI_Range_Check_Fail;

   procedure MSC_Range_Check_Fail  (Big_Int : out Big_Integer; LL_Int : out Long_Long_Integer) is
   begin
      Big_Int := MSC.To_Big_Integer (Long_Long_Integer'Last);
      Big_Int := Big_Int + BI.To_Big_Integer (1);
      LL_Int := MSC.From_Big_Integer (Big_Int); --  @RANGE_CHECK:FAIL
      LL_Int := 0;
   end MSC_Range_Check_Fail;

   procedure MUC_Range_Check_Fail (Big_Int : out Big_Integer; Uns : out Unsigned)  is
   begin
      Big_Int := MUC.To_Big_Integer (Unsigned'Last);
      Big_Int := Big_Int + BI.To_Big_Integer (1);
      Uns := MUC.From_Big_Integer (Big_Int); --  @RANGE_CHECK:FAIL
      Uns := 0;
   end MUC_Range_Check_Fail;

   procedure Divide_Division_Check_Fail (Big_Int : Big_Integer) is
      C : Big_Integer := BI.To_Big_Integer (0);
   begin
      C := Big_Int / C; --  @DIVISION_CHECK:FAIL
   end Divide_Division_Check_Fail;

   procedure Mod_Division_Check_Fail (Big_Int : Big_Integer) is
      C : Big_Integer := BI.To_Big_Integer (0);
   begin
      C := Big_Int mod C; --  @DIVISION_CHECK:FAIL
   end Mod_Division_Check_Fail;

   procedure Rem_Division_Check_Fail (Big_Int : Big_Integer) is
      C : Big_Integer := BI.To_Big_Integer (0);
   begin
      C := Big_Int rem C; --  @DIVISION_CHECK:FAIL
   end Rem_Division_Check_Fail;

   procedure Gcd_Precondition_Fail (Big_Int : Big_Integer) is
      C : Big_Integer := BI.To_Big_Integer (0);
   begin
      C := Greatest_Common_Divisor (Big_Int, C); --  @PRECONDITION:FAIL
   end Gcd_Precondition_Fail;

   A, B, C, D : Big_Integer := BI.To_Big_Integer (1);
   I : Integer;
   Pos : Big_Positive := A;
   Nat : Big_Natural := A;
   LLI : Long_Long_Integer;
   U : Unsigned;

   C_1, C_2 : Integer_255 := (others => 2**28);
   C_3 : Integer_255;

begin
   A := BI.To_Big_Integer (5);
   B := BI.To_Big_Integer (5);
   C := BI.To_Big_Integer (4);
   D := BI.To_Big_Integer (9);

   Nat := A;
   Pos := A;

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

   --  Conversions
   I := To_Integer (A);
   LLI := MSC.From_Big_Integer (A);
   U := MUC.From_Big_Integer (A);

   --  Operators
   A := BI.To_Big_Integer (5);
   B := BI.To_Big_Integer (-5);
   pragma Assert (A + C = D);
   pragma Assert (D - A = C);
   pragma Assert (+B = B);
   pragma Assert (-A = B);
   pragma Assert (abs B = A);
   pragma Assert (A * B = -A * A);
   pragma Assert (B ** 2 = A ** 2);
   pragma Assert (A / B = BI.To_Big_Integer (-1));
   pragma Assert (B mod A = BI.To_Big_Integer (0));
   pragma Assert (A rem B = BI.To_Big_Integer (0));

   --  Functions
   pragma Assert (Min (A, B) = B);
   pragma Assert (Max (B, A) = A);
   pragma Assert (Greatest_Common_Divisor (A, C) = BI.To_Big_Integer (1));

   C_3 := Add (C_1, C_2);
end Big_Integers_Test;
