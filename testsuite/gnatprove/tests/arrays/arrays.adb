package body Arrays is
   function Sum (X : T) return Natural is
      S : Natural := 0;
   begin
      for J in X'Range loop
         S := S + X (J);
      end loop;
      return S;
   end Sum;

   function Count_Even (X : T) return Natural is
      C : Natural := 0;
   begin
      for J in X'Range loop
         if X (J) mod 2 = 0 then
            C := C + 1;
         end if;
      end loop;
      return C;
   end Count_Even;

   function Count_Odd (X : T) return Natural is
      (X'Length - Count_Even (X));

end Arrays;
