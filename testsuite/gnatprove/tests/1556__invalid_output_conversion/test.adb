with Ada.Unchecked_Conversion;

procedure Test with SPARK_Mode is
   type U is mod 256 with Size => 8;
   type P is range 1 .. 127 with Size => 8;
   type A is array (Positive range 1 .. 2) of P;
   type B is new A;

   function To_P is new Ada.Unchecked_Conversion (U, P)
     with Potentially_Invalid;

   procedure Fill (X : out A) with
     Potentially_Invalid => X, Post => True;

   procedure Fill (X : out A) is
   begin
      X := (others => 1);
      X (1) := To_P (0);
   end Fill;

   procedure Update (X : in out A) with
     Potentially_Invalid => X, Post => True;

   procedure Update (X : in out A) is
   begin
      X (1) := To_P (0);
   end Update;

   procedure Fill_Valid (X : out A) with
     Potentially_Invalid => X, Post => X'Valid_Scalars;

   procedure Fill_Valid (X : out A) is
   begin
      X := (others => 1);
   end Fill_Valid;

   procedure Test_Out is
      X : B := (others => 1) with Potentially_Invalid;
   begin
      --  Copy-back through a conversion requires a validity check
      Fill (A (X)); -- @VALIDITY_CHECK:FAIL
   end Test_Out;

   procedure Test_In_Out is
      X : B := (others => 1) with Potentially_Invalid;
   begin
      Update (A (X)); -- @VALIDITY_CHECK:FAIL
   end Test_In_Out;

   procedure Test_Valid_Out is
      X : B := (others => 1) with Potentially_Invalid;
   begin
      Fill_Valid (A (X));
      pragma Assert (X'Valid_Scalars);
   end Test_Valid_Out;

   procedure Test_Direct is
      X : A := (others => 1) with Potentially_Invalid;
   begin
      --  Without a conversion, the validity flag is propagated
      Fill (X);
      pragma Assert (X'Valid_Scalars); -- @ASSERT:FAIL
   end Test_Direct;

begin
   null;
end Test;
