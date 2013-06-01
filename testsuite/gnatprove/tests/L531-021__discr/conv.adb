with Basic;   use Basic;
with Special; use Special;
package body Conv is

   function Id (X : R) return R
      with Post => Id'Result = X;

   function Id (X : R) return R is
   begin
      return X;
   end Id;

   procedure P
   is
      X : Sp := (A, 1, 1);
      Y : R := (A, 1, 1);
      Z : Sp := Id (X);
   begin
      pragma Assert (Id (X) = Id (Y));
   end P;

end Conv;
