package tq is

   type Complex is record
      mReal : Float;
      mImaginary : Float;
   end record;

   function plus (Left, Right: in Complex) return Complex;

   pragma Precondition (Left.mReal > -1000.0 and Left.mReal < 1000.0 and
  	                Left.mImaginary > -1000.0 and Left.mImaginary < 1000.0);

   function eval return Complex;

end tq;

