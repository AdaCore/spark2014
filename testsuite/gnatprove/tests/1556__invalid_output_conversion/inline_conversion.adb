with Ada.Unchecked_Conversion;

procedure Inline_Conversion with SPARK_Mode is
   type U is mod 256 with Size => 8;
   type P is range 1 .. 127 with Size => 8;
   type A is array (Positive range 1 .. 2) of P;
   type B is new A;

   function To_P is new Ada.Unchecked_Conversion (U, P)
     with Potentially_Invalid;

   procedure Fill (X : out A) with Potentially_Invalid => X;

   procedure Fill (X : out A) is
   begin
      X := (others => 1);
      X (1) := To_P (0); -- @VALIDITY_CHECK:FAIL
   end Fill;

   X : B := (others => 1) with Potentially_Invalid;
begin
   --  The conversion result must be checked instead of propagating its flag
   Fill (A (X));
end Inline_Conversion;
