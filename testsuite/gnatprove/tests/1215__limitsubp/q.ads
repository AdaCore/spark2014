package Q is
   function Decrement (X : Integer) return Integer is (X - 1)
     with Pre  => X > Integer'First,
          Post => Decrement'Result = X - 1;
end Q;
