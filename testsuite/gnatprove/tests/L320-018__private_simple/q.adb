with P; use P;

procedure Q is
   Y, Z : T;
begin
   pragma Warnings (Off, "*unused assignment");
   Y := Init;
   Z := Get (Y);
   pragma Warnings (On, "*unused assignment");
   pragma Assert (Z = Y);
end Q;
