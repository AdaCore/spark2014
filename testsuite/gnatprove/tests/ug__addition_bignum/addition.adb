with SPARK.Big_Integers;
use SPARK.Big_Integers;

function Addition (X, Y : Big_Integer) return Big_Integer with
  SPARK_Mode,
  Depends => (Addition'Result => (X, Y)),
  Post    => Addition'Result = X + Y
is
begin
   return X + Y;
end Addition;
