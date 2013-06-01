package Find is
   type A is array (1..10) of Integer;
   function Find (T : A; R : Integer) return Integer
      with Post => Find'Result >= 0 and then
         (if Find'Result /= 0 then T(Find'Result) = R);
end Find;
