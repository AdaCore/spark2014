package body Test
is


   G : Integer;

   procedure Test_01 is
   begin
      G := 0;
   end Test_01;

   procedure Test_02 with Global => (Output => G) is
   begin
      G := 0;
   end Test_02;

   procedure Test_03 with Global => (In_Out => G) is
   begin
      --  error: unused initial value
      G := 0;
   end Test_03;

end Test;
