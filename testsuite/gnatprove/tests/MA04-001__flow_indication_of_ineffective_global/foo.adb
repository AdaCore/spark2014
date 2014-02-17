package body Foo is

   procedure Test_01 is
      My_A : array (1..20) of Integer;
      procedure Local is
      begin
         My_A (1) := 0;
      end Local;
   begin
      Local;
   end Test_01;

   procedure Test_02 (R : out Boolean) is
      My_A : array (1..20) of Integer;
      procedure Local is
      begin
         My_A (1) := 0;
      end Local;
   begin
      Local;
      R := My_A (1) = 0;
   end Test_02;

   G1, G2 : Integer := 0;

   procedure Copy_Stuff (X, Y : out Integer) with
     Global  => (G1, G2),
     Depends => (X => G1,
                 Y => G2)
   is
   begin
      X := G1;
      Y := G2;
   end Copy_Stuff;

   procedure Test_03 (A, B : out Integer) is
   begin
      Copy_Stuff (A, B);
      A := 5;
   end Test_03;


end Foo;
