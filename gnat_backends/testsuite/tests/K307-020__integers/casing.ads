package Casing is

   function F (X : Integer) return Integer
      with Pre => (X < Integer'Last),
           Post => (F'Result = X + 1);

end Casing;
