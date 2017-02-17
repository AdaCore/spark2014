package Base.Annex is pragma SPARK_Mode (On);
   function Mul (x : Integer; y : Integer) return Integer
      with Pre => (0 <= X and then X <= 10 and then 0 <= Y and then Y <= 10);
end Base.Annex;
