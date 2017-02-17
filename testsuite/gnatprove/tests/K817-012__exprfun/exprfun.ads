package Exprfun is

   function Div (X, Y : Integer) return Integer is (X / Y);

   procedure P (X, Y : Integer)
      with Pre => ( Div (X, Y) < 0);

end Exprfun;
