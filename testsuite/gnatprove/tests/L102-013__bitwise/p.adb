procedure P is
   type T is mod 256;
   X, Y : T;
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
