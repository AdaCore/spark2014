procedure Incr (X : in out Integer)
  with SPARK_Mode
is
   X := X + 1;
end Incr;
