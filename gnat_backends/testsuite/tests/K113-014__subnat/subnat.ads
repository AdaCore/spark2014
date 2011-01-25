package Subnat is
   function F (X : Natural) return Integer
      with Post => (F'Result >= 0);
end Subnat;
