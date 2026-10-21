package body Sliding_1
  with SPARK_Mode
is

   --  Each assertion is false at runtime. Only one coordinate is shifted,
   --  so each test isolates one subtraction in the sliding axiom.
   --  Dimension 1 is a control; dimensions 2 onwards expose issue #1508.

   --------------------
   -- Dimension_1_Up --
   --------------------

   procedure Dimension_1_Up is
      type Arr is array (Integer range <>) of Integer;
      A : Arr (0 .. 2) := (10, 20, 30);
      subtype Shifted is Arr (1 .. 3);
      B : constant Shifted := Shifted (A);
   begin
      pragma Assert (B (1) = 30); --@ASSERT:FAIL
   end Dimension_1_Up;

   ----------------------
   -- Dimension_1_Down --
   ----------------------

   procedure Dimension_1_Down is
      type Arr is array (Integer range <>) of Integer;
      A : Arr (0 .. 2) := (10, 20, 30);
      subtype Shifted is Arr (-1 .. 1);
      B : constant Shifted := A;
   begin
      pragma Assert (B (1) = 10); --@ASSERT:FAIL
   end Dimension_1_Down;

end Sliding_1;
