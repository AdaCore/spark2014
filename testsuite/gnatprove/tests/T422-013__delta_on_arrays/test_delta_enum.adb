procedure Test_Delta_Enum with SPARK_Mode is
   type My_Enum is (One, Two, Three, Four, Five);
   type My_Arr is array (My_Enum) of Natural;

   procedure Test1 with Global => null is
      Z : My_Arr := (others => 1);
   begin
      Z := (Z with delta One => 5, Two => 6, Three => 7, One => 1);
      pragma Assert (Z = (1, 6, 7, 1, 1));
   end Test1;

   procedure Test2 with Global => null is
      Z : My_Arr := (others => 1);
   begin
      Z := Z'Update (One => 5, Two => 6, Three => 7, One => 1);
      pragma Assert (Z = (1, 6, 7, 1, 1));
   end Test2;
begin
   null;
end Test_Delta_Enum;
