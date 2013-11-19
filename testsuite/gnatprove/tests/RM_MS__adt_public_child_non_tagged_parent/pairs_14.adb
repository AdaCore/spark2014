package body Pairs_14
  with SPARK_Mode
is
   function Sum (Value : in Pair) return Integer is
     (Value.Value_One + Value.Value_Two);
end Pairs_14;

