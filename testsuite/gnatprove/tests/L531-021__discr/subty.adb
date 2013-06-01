package body Subty is

   procedure P (V : S) is
      Z : S := (A, 1, 1);
   begin
      pragma Assert (Z.X = A);
      pragma Assert (Z.Base = 1);
      pragma Assert (Z.A_Field = 1);
      pragma Assert (V.X = A);

      Z.A_Field := V.A_Field + 1;
      pragma Assert (Z.A_Field = V.A_Field + 1);
      pragma Assert (Z.X = A);
   end P;
end Subty;
