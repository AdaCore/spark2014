with Util;
procedure User (X, Y : out Boolean)
  with Global => (In_Out => Util.S)
is
begin
   X := Util.Get;
   Util.Toggle;
   Y := Util.Get;
   pragma Assert (X = Y);  --  should be unprovable
end User;
