package body Q
is
   G : Integer;

   procedure Test_01 (X : out Integer)
   is
      pragma Global (In_Out => G);
   begin
      X := G;
   end Test_01;

   procedure Test_02 (X : out Integer)
     with Global => (In_Out => G)
   is
   begin
      X := G;
   end Test_02;

   procedure Test_03 (X :    out Integer;
                      G : in out Integer)
   is
   begin
      X := G;
   end Test_03;
end Q;
