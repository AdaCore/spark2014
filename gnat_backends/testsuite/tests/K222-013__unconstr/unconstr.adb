package body Unconstr is

   procedure P (X : out Vec) is
   begin
      X (X'First) := 0;
   end P;

   procedure Q is
      A : Vec (0 .. 10);
   begin
      P (A);
      pragma Assert (A (0) = 1);
   end Q;
end Unconstr;
