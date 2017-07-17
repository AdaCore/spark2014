procedure Dynamic_Float is
   type T is new Float;
begin
   for I in 1 .. 10 loop
      declare
         subtype S is T range 0.0 .. T(I);
         X : S := 1.0;
      begin
         pragma Assert (Integer (S'Last) = I);
         pragma Assert (S'First /= S'Last);
      end;
   end loop;
end Dynamic_Float;
