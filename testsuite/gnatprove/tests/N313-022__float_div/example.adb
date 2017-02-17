pragma SPARK_Mode(On);

package body Example
is

   function Calculate(X : X_T) return Y_T
   is
   begin
      return 43.21 + (1234.5 / X);
   end Calculate;

end Example;
