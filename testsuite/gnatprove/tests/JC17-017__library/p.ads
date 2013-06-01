function P (X : Integer) return Integer
  with Pre  => X >= 0,
       Post => P'Result = X;
