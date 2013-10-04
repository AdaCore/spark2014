with Concat; use Concat;

package body Concat_Right is
   procedure One (X : Integer; Y : UC) is
      Z : UC := Y & X;
   begin
      pragma Assert (Z'First = Y'First);
      pragma Assert (Z (Z'First) = Y (Y'First));
      pragma Assert (Z (Z'Last) = X);
      pragma Assert (Z'Length = Y'Length + 1);
   end One;

   procedure Two (X : Integer; Y : C) is
      Z : C := Y (1 .. 9) & X;
   begin
      pragma Assert (Z (Z'First) = Y'First);
      pragma Assert (Z (Z'Last) = X);
   end Two;

   procedure Three (X : Integer; Y : CB) is
      Z : CB := Y (1 .. 9) & X;
   begin
      pragma Assert (Z (Z'First) = Y'First);
      pragma Assert (Z (Z'Last) = X);
   end Three;

   X : C := (others => 2);
   Y : CB := (others => 2);

   procedure P is
   begin
      One (1, X);
      Two (1, X);
      Three (1, Y);
   end P;

end Concat_Right;
