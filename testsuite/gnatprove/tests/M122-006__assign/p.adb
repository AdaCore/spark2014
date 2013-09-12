with Types; use Types;

package body P is 

   procedure Bad is
      X : R := R'(I => A, X => 1);
   begin
      X := R'(I => B, Y => 2.0);
   end Bad;

   procedure Good is
      X : R := R'(I => A, X => 1);
   begin
      X := R'(I => A, X => 2);
   end Good;

end P;
