package Pck with SPARK_Mode is
  type Random_Integer is range 0 .. Integer'Last;
  --  Integer type for random number generation
  function Random return Random_Integer;
end Pck;
