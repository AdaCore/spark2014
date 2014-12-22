package Sqrt
  with SPARK_Mode
is
  -- The function below calculates the square root of a
  -- natural number.

   function SQRT (N : in Natural) return Natural
     with Post => SQRT'Result * SQRT'Result <= N and
                  (SQRT'Result + 1) * (SQRT'Result + 1) > N;

end Sqrt;
