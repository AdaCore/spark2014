package B is
   function F return Integer
      with Post => (F'Result = 2);
end B;
