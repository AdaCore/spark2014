package body Expr is
   function Echo (A : Integer) return Integer is
      R : Integer;
   begin
      R := Echo2 (A);
      return R;
   end Echo;
end Expr;
