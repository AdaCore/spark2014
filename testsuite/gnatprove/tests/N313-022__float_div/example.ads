pragma SPARK_Mode(On);

package Example
is
   type Float_T is digits 15 range -3.40282E+38 ..  3.40282E+38;
   for Float_T'Size use 64;

   X_min : constant Float_T := 10.0;
   X_max : constant Float_T := 50.0;

   subtype X_T is Float_T range X_min .. X_max;

   subtype Y_T is Float_T
   range (43.21 + 1234.5 / X_T'Last)
     .. (43.21 + 1234.5 / X_T'First);

   function Calculate(X : X_T) return Y_T;

end Example;
