package body Triangle is

   function Sum_Up_To (N : Natural) return Natural is
      Tmp : Natural := 0;
   begin
      for I in 1 .. N loop
         Tmp := Tmp + I;
         pragma Loop_Invariant (Tmp = I * (I + 1) / 2);
      end loop;
      return Tmp;
   end Sum_Up_To;
end Triangle;
