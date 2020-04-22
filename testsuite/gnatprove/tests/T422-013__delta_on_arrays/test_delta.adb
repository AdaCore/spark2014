procedure Test_Delta with SPARK_Mode is
   type My_Arr is array (Positive range <>) of Natural;

   procedure Test1 with Global => null is
      Z : My_Arr := (1 .. 5 => 1);
   begin
      Z := (Z with delta 1 => 5, 2 => 6, 3 => 7, 1 => 1);
      pragma Assert (Z = (1, 6, 7, 1, 1));
   end Test1;

   procedure Test2 with Global => null is
      Z : My_Arr := (1 .. 5 => 1);
   begin
      Z := Z'Update (1 => 5, 2 => 6, 3 => 7, 1 => 1);
      pragma Assert (Z = (1, 6, 7, 1, 1));
   end Test2;
begin
   null;
end Test_Delta;
