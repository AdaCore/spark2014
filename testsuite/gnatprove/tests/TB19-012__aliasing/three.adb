procedure Three is

   X : Integer;
   Y : Integer with Import, Address => X'Address;
   Z : Integer with Import, Address => Y'Address;
begin
   X := 0;
   pragma Assert (X = 0);
   Y := 0;
   Z := 0;
   pragma Assert (Y = 0);
   pragma Assert (Z = 0);
end Three;
