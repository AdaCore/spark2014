with Interfaces; use Interfaces;

procedure Bitwise_Swap (X, Y : in out Unsigned_32) with
  Post => X = Y'Old and Y = X'Old,
  SPARK_Mode
is
begin
   X := X xor Y;
   Y := X xor Y;
--  Uncomment the following line to prove
-- X := X xor Y;
end Bitwise_Swap;
