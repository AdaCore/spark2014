with Ada.Unchecked_Conversion;

procedure Inline_Copy with SPARK_Mode is
   type U is mod 65536 with Size => 16;
   type P is range 1 .. 127 with Size => 8;
   type A is array (Positive range 1 .. 2) of P;
   type B is new A;

   function To_A is new Ada.Unchecked_Conversion (U, A)
     with Potentially_Invalid;

   Y : A := To_A (0) with Potentially_Invalid;

   procedure Fill (X : out A) with Potentially_Invalid => X;

   procedure Fill (X : out A) is
   begin
      X := Y; -- @VALIDITY_CHECK:FAIL
   end Fill;

   X : B := (others => 1) with Potentially_Invalid;
begin
   --  Inlining makes the assignment target a conversion of X
   Fill (A (X));
end Inline_Copy;
