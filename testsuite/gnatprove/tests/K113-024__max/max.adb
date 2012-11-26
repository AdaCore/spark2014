package body Max is
   function Max (T : A) return Integer is
      Imax : Integer := T (1);
   begin
      for I in Integer range 2 .. 10 loop
         pragma Loop_Invariant (T (1) <= Imax);
         if T (I) > Imax then
            Imax := T (I);
         end if;
      end loop;
      return Imax;
   end Max;
end Max;
