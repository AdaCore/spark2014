with Interfaces; use Interfaces;

procedure Conv (X : Unsigned_32) is
   XX : Unsigned_128 := Unsigned_128(X);
   Y  : Unsigned_32 := Unsigned_32(XX);
begin
   pragma Assert (X = Y);
end Conv;
