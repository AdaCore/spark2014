function Addition (X, Y : Integer) return Integer with
  SPARK_Mode,
  Depends => (Addition'Result => (X, Y)),
  Pre     => X + Y in Integer,
  Post    => Addition'Result = X + Y
is
begin
   return X + Y;
end Addition;
