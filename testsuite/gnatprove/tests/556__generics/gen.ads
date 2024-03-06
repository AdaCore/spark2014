package Gen with SPARK_Mode is

  type T is range 1 .. 100;
  generic
    X : in Integer;
  function F return Integer
    with Post => F'Result = X;
end Gen;
