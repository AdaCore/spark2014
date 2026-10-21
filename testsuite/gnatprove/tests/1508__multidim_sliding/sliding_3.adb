package body Sliding_3
  with SPARK_Mode
is

   --  Each assertion is false at runtime. Only one coordinate is shifted,
   --  so each test isolates one subtraction in the sliding axiom.
   --  Dimension 1 is a control; dimensions 2 onwards expose issue #1508.

   --------------------
   -- Dimension_1_Up --
   --------------------

   procedure Dimension_1_Up is
      type Arr is
        array (Integer range <>,
               Integer range <>,
               Integer range <>)
        of Integer;
      A : Arr (0 .. 2, 1 .. 1, 1 .. 1) :=
        (0 => (1 => (1 => 10)), 1 => (1 => (1 => 20)), 2 => (1 => (1 => 30)));
      subtype Shifted is Arr (1 .. 3, 1 .. 1, 1 .. 1);
      B : constant Shifted := Shifted (A);
   begin
      pragma Assert (B (1, 1, 1) = 30); --@ASSERT:FAIL
   end Dimension_1_Up;

   ----------------------
   -- Dimension_1_Down --
   ----------------------

   procedure Dimension_1_Down is
      type Arr is
        array (Integer range <>,
               Integer range <>,
               Integer range <>)
        of Integer;
      A : Arr (0 .. 2, 1 .. 1, 1 .. 1) :=
        (0 => (1 => (1 => 10)), 1 => (1 => (1 => 20)), 2 => (1 => (1 => 30)));
      subtype Shifted is Arr (-1 .. 1, 1 .. 1, 1 .. 1);
      B : constant Shifted := A;
   begin
      pragma Assert (B (1, 1, 1) = 10); --@ASSERT:FAIL
   end Dimension_1_Down;

   --------------------
   -- Dimension_2_Up --
   --------------------

   procedure Dimension_2_Up is
      type Arr is
        array (Integer range <>,
               Integer range <>,
               Integer range <>)
        of Integer;
      A : Arr (1 .. 1, 0 .. 2, 1 .. 1) :=
        (1 => (0 => (1 => 10), 1 => (1 => 20), 2 => (1 => 30)));
      subtype Shifted is Arr (1 .. 1, 1 .. 3, 1 .. 1);
      B : constant Shifted := Shifted (A);
   begin
      pragma Assert (B (1, 1, 1) = 30); --@ASSERT:FAIL
   end Dimension_2_Up;

   ----------------------
   -- Dimension_2_Down --
   ----------------------

   procedure Dimension_2_Down is
      type Arr is
        array (Integer range <>,
               Integer range <>,
               Integer range <>)
        of Integer;
      A : Arr (1 .. 1, 0 .. 2, 1 .. 1) :=
        (1 => (0 => (1 => 10), 1 => (1 => 20), 2 => (1 => 30)));
      subtype Shifted is Arr (1 .. 1, -1 .. 1, 1 .. 1);
      B : constant Shifted := A;
   begin
      pragma Assert (B (1, 1, 1) = 10); --@ASSERT:FAIL
   end Dimension_2_Down;

   --------------------
   -- Dimension_3_Up --
   --------------------

   procedure Dimension_3_Up is
      type Arr is
        array (Integer range <>,
               Integer range <>,
               Integer range <>)
        of Integer;
      A : Arr (1 .. 1, 1 .. 1, 0 .. 2) := (1 => (1 => (10, 20, 30)));
      subtype Shifted is Arr (1 .. 1, 1 .. 1, 1 .. 3);
      B : constant Shifted := Shifted (A);
   begin
      pragma Assert (B (1, 1, 1) = 30); --@ASSERT:FAIL
   end Dimension_3_Up;

   ----------------------
   -- Dimension_3_Down --
   ----------------------

   procedure Dimension_3_Down is
      type Arr is
        array (Integer range <>,
               Integer range <>,
               Integer range <>)
        of Integer;
      A : Arr (1 .. 1, 1 .. 1, 0 .. 2) := (1 => (1 => (10, 20, 30)));
      subtype Shifted is Arr (1 .. 1, 1 .. 1, -1 .. 1);
      B : constant Shifted := A;
   begin
      pragma Assert (B (1, 1, 1) = 10); --@ASSERT:FAIL
   end Dimension_3_Down;

end Sliding_3;
