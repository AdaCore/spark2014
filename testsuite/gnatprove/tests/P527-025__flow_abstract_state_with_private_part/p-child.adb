package body P.Child is

   procedure Test_01 is
   begin
      X := 0;
   end Test_01;

   procedure Test_02 is
   begin
      X := 0;
   end Test_02;

   --  X is not a valid refinement (see 7.2.4(3d))
   procedure Test_03
   with Refined_Global => (Output => State)
   is
   begin
      X := 0;
   end Test_03;

   procedure Test_04 is
   begin
      Test_01;
   end Test_04;

   --  X is not a valid refinement (see 7.2.4(3d))
   procedure Test_05
   with Refined_Global => (Output => State)
   is
   begin
      Test_01;
   end Test_05;

end P.Child;
