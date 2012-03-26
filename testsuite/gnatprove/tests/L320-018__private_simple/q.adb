with P; use P;
procedure Q is
   Y, Z : T;
begin
   Z := Get (Y);
   pragma Assert (Y = Z);
end Q;
