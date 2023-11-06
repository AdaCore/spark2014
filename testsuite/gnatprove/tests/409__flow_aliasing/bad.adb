procedure Bad (B : in out Integer) is

   function Increment_And_Return (X : in out Integer) return Integer with
     Side_Effects, Global => null, Pre => True;

   function Increment_And_Return (X : in out Integer) return Integer is
   begin
      X := X + 1;
      return X;
   end Increment_And_Return;

   type Arr is array (1 .. 3) of Integer;
   A : Arr;
begin
   A (B) := Increment_And_Return (B);
   pragma Assert (B = A (B));
end Bad;
