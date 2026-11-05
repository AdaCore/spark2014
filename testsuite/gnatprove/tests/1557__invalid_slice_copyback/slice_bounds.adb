with Ada.Unchecked_Conversion;

procedure Slice_Bounds with SPARK_Mode is
   type U is mod 256 with Size => 8;
   type P is range 1 .. 127 with Size => 8;
   type A is array (Positive range <>) of P;

   function To_P is new Ada.Unchecked_Conversion (U, P)
     with Potentially_Invalid;

   procedure Update (X : in out A; Lo, Hi : out Positive) with
     Global => null, Potentially_Invalid => X,
     Pre => X'Length = 2, Post => Lo = 3 and Hi = 4;

   procedure Update (X : in out A; Lo, Hi : out Positive) is
   begin
      X (X'First) := To_P (0);
      Lo := 3;
      Hi := 4;
   end Update;

   X : A (1 .. 4) := (others => 1) with Potentially_Invalid;
   Lo : Positive := 1;
   Hi : Positive := 2;
begin
   Update (X (Lo .. Hi), Lo, Hi);
   --  The original slice can become invalid; the other elements stay valid
   pragma Assert (X (3 .. 4)'Valid_Scalars);
   pragma Assert (X (1 .. 2)'Valid_Scalars); -- @ASSERT:FAIL
end Slice_Bounds;
