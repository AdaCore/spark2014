package body Gene is

   function Sat_Div (A : Integer) return Integer is
   begin
      if X = 0 then
         return 0;
      else
         return A / X;
      end if;
   end Sat_Div;

end Gene;
