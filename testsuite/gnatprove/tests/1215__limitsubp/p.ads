package P is
   function Increment (X : Integer) return Integer is (X + 1)
     with Pre  => X < Integer'Last,
          Post => Increment'Result = X + 1;
end P;
