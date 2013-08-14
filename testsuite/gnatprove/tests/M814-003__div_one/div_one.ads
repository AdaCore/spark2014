package Div_One is

   function F (A : Positive) return Positive
      with Post => (F'Result / A = 1);

end Div_One;
