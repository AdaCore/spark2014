package Expr is
   function Echo (A : Integer) return Integer
   with Post => (Echo'Result = A);

   function Echo2 (A : Integer) return Integer is (A);
end Expr;
