package Pre is

   type I is range 1 .. 10;
   type A is array (I) of Integer;

   function Pred (X : I) return Boolean;

   procedure P (Z : I)
      with Pre => (for all X in I'Range => Pred (X));

end Pre;
