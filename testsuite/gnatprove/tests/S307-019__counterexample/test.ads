package Test is
   pragma SPARK_Mode(On);

  function Test (X : Integer) return Integer
    with Post => Test'Result = 1;

end Test;
