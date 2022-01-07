package body T3Q2
is

   function Double (X: in Natural) return Natural
     with Pre => (X <= Natural'Last/2),
     Post => (Double'Result = 2 * X);

   function Double (X: in Natural) return Natural
   --# pre    X <= Natural'Last/2;
   --# return 2 * X;
   is
   begin
      return 2 * X;
   end Double;

   function Quadruple (X: in Natural) return Natural
   is
      T : Natural;
   begin
      T := Double (Double (X));
      pragma Assert (T = 2 * (2 * X));
      return T;
   end Quadruple;

end T3Q2;
