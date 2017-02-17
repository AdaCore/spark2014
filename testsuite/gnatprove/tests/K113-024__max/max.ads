package Max is
   type A is array (1..10) of Integer;
   function Max (T : A) return Integer
      with Post => T (1) <= Max'Result;
end Max;
