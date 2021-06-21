with P; use P;

procedure Main2 is
begin
   X := 0;
   Y := 0;
   Z := 0;

   pragma Assert (X = 0 and Y = 0 and Z = 0);

   X := 1;
   pragma Assert (Y = 0); --@ASSERT:FAIL
end;
