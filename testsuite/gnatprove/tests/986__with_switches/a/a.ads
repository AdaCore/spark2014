package A is

  function Incr (X : Integer) return Integer is (X + 1) with Pre => X < Integer'Last;
end A;
