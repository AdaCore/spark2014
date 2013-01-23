package Nobody is
   function Divide (X, Y : Integer) return Integer with
     Pre  => Y /= 0,
     Post => Divide'Result = X / Y;
end Nobody;
