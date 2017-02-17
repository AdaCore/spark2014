package Base is pragma SPARK_Mode (On);
   function Double (x : Integer) return Integer
      with Pre => (X = 3);
end Base;
