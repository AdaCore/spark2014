package body Minus is

   function Minus (X : Natural) return Natural is
   begin
      if X = 1 then
         return 0;
      elsif X = 2 then
         return 1;
      elsif X = 3 then
         return 2;
      end if;

      return X;
   end Minus;

end Minus;
