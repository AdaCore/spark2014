with Interfaces; use Interfaces;

procedure Swap_Modulo (X, Y : in out Unsigned_32) with
  SPARK_Mode,
  Depends => (X => Y, Y => X),
  Post    => X = Y'Old and Y = X'Old
is
begin
   X := X xor Y;
   Y := X xor Y;
   X := X xor Y;
end Swap_Modulo;
