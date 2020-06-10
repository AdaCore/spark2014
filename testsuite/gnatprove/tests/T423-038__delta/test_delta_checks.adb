procedure Test_Delta_Checks with SPARK_Mode is
   type My_Arr is array (Positive range <>) of Natural;

   X : Positive := 10;
   Y : Positive := 10;

   procedure Test1 with Global => (Input => Y) is
      Z : My_Arr := (1 .. 5 => 1);
   begin
      Z := (Z with delta Y => 1, 1 => 5, 2 => 6, 3 => 7, 1 => 1);--@INDEX_CHECK:FAIL
      pragma Assert (Z = (1, 6, 7, 1, 1));
   end Test1;

   procedure Test2 with Global => (Input => Y) is
      Z : My_Arr := (1 .. 5 => 1);
   begin
      Z := Z'Update (Y => 1, 1 => 5, 2 => 6, 3 => 7, 1 => 1);--@INDEX_CHECK:FAIL
      pragma Assert (Z = (1, 6, 7, 1, 1));
   end Test2;

   procedure Test3 with Global => (Input => Y) is
      C : constant positive := Y;

      type Matrice is array (1 .. 5, 1 .. 5) of Natural;
      Z : Matrice := (1 .. 5 => (1 .. 5 => 1));
   begin
      Z := Z'Update ((Y, 5) => 1);--@RANGE_CHECK:FAIL
      null;
   end Test3;
begin
   Test2;
end Test_Delta_Checks;
