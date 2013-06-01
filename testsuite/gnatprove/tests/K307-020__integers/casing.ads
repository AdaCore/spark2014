package Casing is

   function F (X : Integer) return Integer
      with Pre => (X < Integer'Last),
           Post => (F'Result = X + 1);

   function G (X : Integer) return Integer
      with Pre => (X < Integer'Last),
           Post => (G'Result = X + 1);
end Casing;
