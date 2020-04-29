procedure Test_Delta_Checks with SPARK_Mode is
   type My_Pos is new Positive;
   type My_Arr is array (My_Pos range <>) of Natural;

   Y : My_Pos range 2 .. My_Pos'Base'Last := 10;

   procedure Test1 with Global => (Input => Y) is
      Z : My_Arr := (1 .. 5 => 1);
   begin
      Z := (Z with delta Y .. 1 => 0);
      pragma Assert (Z = (1, 1, 1, 1, 1));
   end Test1;

   procedure Test2 with Global => (Input => Y) is
      Z : My_Arr := (1 .. 5 => 1);
   begin
      Z := Z'Update (Y .. 1 => 0);
      pragma Assert (Z = (1, 1, 1, 1, 1));
   end Test2;

   procedure Test3 with Global => (Input => Y) is
      Z : My_Arr := (1 .. 5 => 1);
   begin
      Z := (Z with delta Y => 1, 1 => 5, 2 => 6, 3 => 7, 1 => 1); --@INDEX_CHECK:FAIL
      pragma Assert (Z = (1, 6, 7, 1, 1));
   end Test3;

   procedure Test4 with Global => (Input => Y) is
      Z : My_Arr := (1 .. 5 => 1);
   begin
      Z := (Z with delta 3 .. Y => 1, 1 => 5, 2 => 6, 3 => 7, 1 => 1); --@INDEX_CHECK:FAIL
      pragma Assert (Z = (1, 6, 7, 1, 1));
   end Test4;

   procedure Test5 with Global => (Input => Y) is
      Z : My_Arr := (1 .. 5 => 1);
   begin
      Z := (Z with delta Y | 3 => 1, 1 => 5, 2 => 6, 3 => 7, 1 => 1); --@INDEX_CHECK:FAIL
      pragma Assert (Z = (1, 6, 7, 1, 1));
   end Test5;

   procedure Test6 with Global => (Input => Y) is
      type My_Mat is array (My_Pos range 1 .. 5, My_Pos range 1 .. 5) of Integer;
      Z : My_Mat := (others => (others => 1));
   begin
      Z := Z'Update ((Y, 1) | --@INDEX_CHECK:FAIL
                     (1, Y) => 1); --@INDEX_CHECK:FAIL
      pragma Assert (Z = (1 .. 5 => (1 .. 5 => 1)));
   end Test6;
begin
   Test1;
   Test2;
end Test_Delta_Checks;
