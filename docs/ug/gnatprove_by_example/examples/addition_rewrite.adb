function Addition_Rewrite (X, Y : Integer) return Integer with
  SPARK_Mode,
  Depends => (Addition_Rewrite'Result => (X, Y)),
  Pre     => (X >= 0 and then Y <= Integer'Last - X) or else (X < 0 and then Y >= Integer'First - X),
  Post    => Addition_Rewrite'Result = X + Y
is
begin
   return X + Y;
end Addition_Rewrite;
