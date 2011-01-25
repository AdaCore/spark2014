package Subnat is
   function F (X : Natural) return Integer
      with Post => (F'Result >= 0);

   function G ( X : Integer) return Positive
      with Pre => (X >= 1);
end Subnat;
