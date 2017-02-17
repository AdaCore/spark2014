with Types; use Types;

package body P is

   procedure Good is
      X : R := R'(I => A, X => 1);
   begin
      X := R'(I => A, X => 2);
   end Good;

   procedure Good_2 is
      X : R := R'(I => A, X => 1);
   begin
      X := R'(I => B, Y => 2.0);
   end Good_2;

end P;
