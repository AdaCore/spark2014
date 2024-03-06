package body Gen with SPARK_Mode is

  function G (X : Integer) return Integer is (X);

  function F return Integer is (G (X));

end Gen;
