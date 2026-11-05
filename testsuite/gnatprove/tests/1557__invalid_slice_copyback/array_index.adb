with Ada.Unchecked_Conversion;

procedure Array_Index with SPARK_Mode is
   type U is mod 256 with Size => 8;
   type P is range 1 .. 127 with Size => 8;
   type R is record
      F : P;
   end record;
   type A is array (Positive range 1 .. 4) of R;

   function To_P is new Ada.Unchecked_Conversion (U, P)
     with Potentially_Invalid;

   procedure Update (X : in out R; I : out Positive) with
     Global => null, Potentially_Invalid => X, Post => I = 3;

   procedure Update (X : in out R; I : out Positive) is
   begin
      X.F := To_P (0);
      I := 3;
   end Update;

   X : A := (others => (F => 1)) with Potentially_Invalid;
   I : Positive := 1;
begin
   --  Indexed-component updates must also use the index captured before the call
   Update (X (I), I);
   pragma Assert (X (2 .. 4)'Valid_Scalars);
   pragma Assert (X (1)'Valid_Scalars); -- @ASSERT:FAIL
end Array_Index;
