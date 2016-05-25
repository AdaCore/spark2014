with Init; use Init;

procedure Use_Init with
   Global => (State,
              B,
              C,
              E)
is
   XB : Integer;
   XC : Integer;
   XE : Integer;
begin
   XB := B;
   XC := C;
   XE := E;
end Use_Init;
