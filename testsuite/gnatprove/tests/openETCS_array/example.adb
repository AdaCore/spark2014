package body Example is pragma SPARK_Mode (On);
   function Saturated_Sum(X1, X2, Maximum : Natural) return Natural is
   begin
      if X1 + X2 <= Maximum then
         return X1 + X2;
      else
         return Maximum;
      end if;
   end Saturated_Sum;
end Example;
