package protectedFloat is pragma SPARK_Mode (On);

   type Real is digits 6;

   function protectedRealDivide( left, right : in Real) return Real
     with pre => ((left >= 0.0) and (right >= 0.0));

end protectedFloat;
