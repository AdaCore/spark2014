package Check is
   function Div (X, Y : Integer) return Integer
      with Pre => (X /= 0 and then 1/X > 0 and then Y /= 0 and then 1/Y > 0),
           Post => (Div'Result > 0);
end Check;
