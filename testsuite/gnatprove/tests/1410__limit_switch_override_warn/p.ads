package P is
   function Increment (X : Integer) return Integer
   with Pre => X < Integer'Last, Post => Increment'Result = X + 1;
   function Decrement (X : Integer) return Integer
   with Pre => X > Integer'First, Post => Decrement'Result = X - 1;
end P;
