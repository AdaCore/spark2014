
package body tq is

   function plus (Left, Right: in Complex) return Complex
   is
   begin
      return (
             	mReal => Left.mReal + Right.mReal,
                mImaginary => Left.mImaginary + Right.mImaginary

              );
   end plus;

   function eval return Complex
   is
      mCplex1 : constant Complex := (mReal => 2.0,
                                    mImaginary => 3.0);
      mCplex2 : constant Complex := (mReal => 4.0,
                                    mImaginary => 4.0);
      sumCplex : Complex;
   begin
      sumCplex := plus(mCplex1, mCplex2);

      return sumCplex;
   end eval;

end tq;

