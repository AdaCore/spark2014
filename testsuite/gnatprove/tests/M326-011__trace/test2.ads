package Test2 is

  function Test (X : Integer) return Integer
    with Post => Test'Result = 1;

end Test2;
