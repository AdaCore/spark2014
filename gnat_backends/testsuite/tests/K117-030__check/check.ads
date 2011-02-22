package Check is
   function Div (X : Integer) return Integer
      with Pre => (X /= 0 and then 1/X > 0),
           Post => (Div'Result > 0);
end Check;
