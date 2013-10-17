package body Concat is

   procedure One (A, B : C) is
      D : C := A (6 .. 10) & B (1 .. 5);
   begin
      pragma Assert (D (1) = A (6));
      pragma Assert (D (6) = B (1));
   end One;

   procedure Two (A, B : CB) is
      D : CB := A (6 .. 10) & B (1 .. 5);
   begin
      pragma Assert (D (1) = A (6));
      pragma Assert (D (6) = B (1));
   end Two;

   procedure Three (A, B : UC) is
      D : UC := A & B;
   begin
      pragma Assert (D'First = A'First);
      pragma Assert (D'Length = A'Length + B'Length);
      pragma Assert (D'Last = A'First + A'Last + 1 + (B'Last - B'First));
   end Three;

   X : C := (others => 2);
   Y : CB := (others => 2);

   procedure P is begin
      One (X, X);
      Two (Y, Y);
      Three (X, X);
   end P;

end Concat;
