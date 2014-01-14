procedure Dynamic_Fixed is
   type T is delta 0.5 range 0.0 .. 10.0;
begin
   for I in 1 .. 10 loop
      declare
         subtype S is T range 0.0 .. T(I);
         X : S := 1.0;
      begin
         pragma Assert (Integer (T'Last) = I);
         pragma Assert (T'First /= T'Last);
      end;
   end loop;
end Dynamic_Fixed;

