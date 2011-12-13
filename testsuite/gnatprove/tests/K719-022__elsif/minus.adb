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

   function Minus2 (X : Natural) return Natural is
   begin
      return
         (if X = 1 then 0 elsif X = 2 then 1 elsif X = 3 then 2 else X);
   end Minus2;

end Minus;
