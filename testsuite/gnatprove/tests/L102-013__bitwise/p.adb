procedure P (Havok_X, Havok_Y : Natural) is
   type T is mod 256;
   X : T := T (Havok_X mod 256);
   Y : T := T (Havok_Y mod 256);
begin
   if (X and Y) < X then
      null;
   end if;
   if (X or Y) < X then
      null;
   end if;
   if (X xor Y) < X then
      null;
   end if;
end P;
