with Concat; use Concat;

package body Concat_Left is
   procedure One (X : Integer; Y : UC) is
      Z : UC := X & Y;
   begin
      pragma Assert (Z'First = Integer'First);
      pragma Assert (Z (Z'First) = X);
      pragma Assert (Z'Length = Y'Length + 1);
   end One;

   procedure Two (X : Integer; Y : C) is
      Z : C := X & Y (1 .. 9);
   begin
      pragma Assert (Z (Z'First) = X);
      pragma Assert (Z (10) = Y (9));
   end Two;

   procedure Three (X : Integer; Y : CB) is
      Z : CB := X & Y (1 .. 9);
   begin
      pragma Assert (Z (Z'First) = X);
      pragma Assert (Z (10) = Y (9));
   end Three;

   X : C := (others => 2);
   Y : CB := (others => 2);

   procedure P is
   begin
      One (1, X);
      Two (1, X);
      Three (1, Y);
   end P;

end Concat_Left;
