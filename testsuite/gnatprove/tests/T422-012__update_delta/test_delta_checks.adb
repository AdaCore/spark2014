procedure Test_Delta_Checks with SPARK_Mode is
   type My_Enum is (One, Two, Three, Four, Five);
   type My_Arr is array (My_Enum) of Natural;

   X : Integer;

   procedure Test1 with Global => (Input => X) is
      Z : My_Arr := (others => 1);
   begin
      Z := (Z with delta One => X, Two => 6, Three => 7, One => 1); --@RANGE_CHECK:FAIL
      pragma Assert (Z = (1, 6, 7, 1, 1));
   end Test1;

   procedure Test2 with Global => (Input => X) is
      Z : My_Arr := (others => 1);
   begin
      Z := Z'Update (One => X, Two => 6, Three => 7, One => 1); --@RANGE_CHECK:FAIL
      pragma Assert (Z = (1, 6, 7, 1, 1));
   end Test2;
begin
   null;
end Test_Delta_Checks;
