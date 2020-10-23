with Ada.Numerics.Big_Numbers.Big_Integers; use Ada.Numerics.Big_Numbers.Big_Integers;

procedure Diff3 is

   type U128 is mod 2**128 with
     Annotate => (GNATprove, No_Wrap_Around);

   function U_Exp_Gt0 (J : Natural) return Boolean with
     Pre => J in 0 .. 127
    is
      X : constant U128 := 2**J;  -- @OVERFLOW_CHECK:PASS
      pragma Assert (X > 0);
      Y : constant U128 := 2**(J+1);  -- @OVERFLOW_CHECK:FAIL
   begin
      return True;
   end U_Exp_Gt0;

   function U_Exp_Const_Trans (J : Natural) return Boolean with
     Pre => J in 0 .. 8
    is
      Pow2_J  : constant U128 := 2**J;
   begin
      pragma Assert (Pow2_J = 2**J);
      pragma Assert (2**J > 0);
      pragma Assert (Pow2_J > 0);
      return True;
   end U_Exp_Const_Trans;

   pragma Warnings (Off, "no Global contract available for ""*""");

   package U_Conversions is new Unsigned_Conversions (U128);

   function U_Exp_BI_Trans (J : Natural) return Boolean with
     Pre => J in 0 .. 8
    is
      Pow2_J  : constant U128 := 2**J;
      Y : constant U128 := Pow2_J / 2;
   begin
      pragma Assert (Y <= 2**J);
      pragma Assert (U_Conversions.To_Big_Integer (Y) <= To_Big_Integer (2)**J);
      return True;
   end U_Exp_BI_Trans;
begin
   null;
end;
