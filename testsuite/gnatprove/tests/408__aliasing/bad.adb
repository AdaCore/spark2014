procedure Bad is
   H : Integer;

   function Increment_And_Return (X, Y : in out Integer) return Integer
     with Side_Effects, Global => (In_Out => H);

   function Increment_And_Return (X, Y : in out Integer) return Integer is
   begin
      X := X + 1;
      Y := Y + 1;
      H := H + 1;
      return 0;
   end;

   V : Integer;
begin
   V := Increment_And_Return (V, H); -- @ALIASING:CHECK
   pragma Assert (V = H);
end;
