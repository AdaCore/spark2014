package Test is

  function Test (X : Integer) return Integer
    with Post => Test'Result = 1;

end Test;
