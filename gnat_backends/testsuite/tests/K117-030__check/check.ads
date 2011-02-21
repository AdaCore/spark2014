package Check is
   function Div (X : Integer) return Integer
      with Pre => (1/X > 0),
           Post => (Div'Result > 0);
end Check;
