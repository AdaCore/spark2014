package body Unconstr is

   procedure P (X : out Vec) is
   begin
      X := (others => 0);
   end P;

   procedure Q is
      A : Vec_10_Sub;
   begin
      P (A);
      pragma Assert (A (0) = 1);
   end Q;

   procedure R is
      A : Vec_10;
   begin
      P (Vec (A));
      pragma Assert (A (0) = 1);
   end R;
end Unconstr;
