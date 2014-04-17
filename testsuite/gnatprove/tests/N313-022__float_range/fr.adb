procedure FR with
  SPARK_Mode
is
   subtype Float1 is Float range 0.5 .. 0.9;
   subtype Float2 is Float range 0.0 .. 2.1;
   X : Float1;
   Y : Float1;
   Z : Float2;

   procedure Test_Add with Pre => True is
   begin
      Z := X + 0.1              --  @OVERFLOW_CHECK:PASS
             + Y                --  @OVERFLOW_CHECK:PASS
             + 0.2;             --  @OVERFLOW_CHECK:PASS @RANGE_CHECK:PASS
      Z := X + 0.1 + Y + 0.21;  --  @RANGE_CHECK:FAIL
   end Test_Add;

   procedure Test_Subtract with Pre => True is
   begin
      Z := X - 0.3              --  @OVERFLOW_CHECK:PASS
             - 0.19;            --  @OVERFLOW_CHECK:PASS @RANGE_CHECK:PASS
      Z := X - 0.3 - 0.2;       --  @RANGE_CHECK:FAIL
   end Test_Subtract;

   procedure Test_Mult with Pre => True is
   begin
      Z := 2.33 * X;            --  @OVERFLOW_CHECK:PASS @RANGE_CHECK:PASS
      Z := 2.34 * X;            --  @RANGE_CHECK:FAIL
   end Test_Mult;

   procedure Test_Div with Pre => True is
   begin
      Z := X / Y;               --  @OVERFLOW_CHECK:PASS @RANGE_CHECK:PASS
      Z := X / 0.42;            --  @RANGE_CHECK:FAIL
   end Test_Div;

begin
   X := 0.9;
   Y := 0.9;
   Z := 0.0;
   Test_Add;
   X := 0.5;
   Test_Subtract;
   X := 0.9;
   Test_Mult;
   Y := 0.5;
   Test_Div;
end FR;
