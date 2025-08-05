package C is

  function Incr (X : Integer) return Integer is (X + 1) with Pre => X < Integer'Last;
end C;
