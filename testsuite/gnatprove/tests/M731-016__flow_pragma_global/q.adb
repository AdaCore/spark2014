package body Q is

   G : Integer;

   procedure Test_01 (X : out Integer);
   pragma Global (Input => G);

   procedure Test_01 (X : out Integer)
   is
   begin
      X := G;
      G := G + 1;
   end Test_01;

   procedure Test_02 (X : out Integer)
   is
      pragma Global (Input => G);
   begin
      X := G;
      G := G + 1;
   end Test_02;

   procedure Test_03 (X : out Integer)
   with Global => G
   is
   begin
      X := G;
      G := G + 1;
   end Test_03;

end Q;
