procedure Others_Choices with SPARK_Mode is
   type Vector is array (Positive range <>) of Integer;
   type Matrix is array (Positive range <>, Positive range <>) of Integer;

   procedure Named is
      A : constant Vector (1 .. 3) :=
        [1 => 0, for I in others => 10 / (I - 1)]; --  @DIVISION_CHECK:PASS
   begin
      pragma Assert (A (1) = 0 and A (2) = 10 and A (3) = 5); --  @ASSERT:PASS
   end Named;

   procedure Ranges is
      A : constant Vector (1 .. 5) :=
        [1 .. 2 | 4 => 0, for I in others => 12 / (I - 2)]; --  @DIVISION_CHECK:PASS
   begin
      pragma Assert (A (3) = 12 and A (4) = 0 and A (5) = 4); --  @ASSERT:PASS
   end Ranges;

   procedure Positional is
      A : constant Vector (5 .. 8) :=
        [0, 0, for I in others => 12 / (I - 6)]; --  @DIVISION_CHECK:PASS
   begin
      pragma Assert (A (5) = 0 and A (7) = 12 and A (8) = 6); --  @ASSERT:PASS
   end Positional;

   procedure Modular_Positional is
      type Index is mod 7;
      type Modular_Vector is array (Index range <>) of Integer;
      A : constant Modular_Vector (3 .. 6) :=
        [0, 0, for I in others => 12 / Integer (I - 4)]; --  @DIVISION_CHECK:PASS
   begin
      pragma Assert (A (3) = 0 and A (5) = 12 and A (6) = 6); --  @ASSERT:PASS
   end Modular_Positional;

   procedure Nested is
      A : constant Matrix (1 .. 2, 1 .. 3) :=
        [for I in 1 .. 2 =>
           [1 => 0, for J in others => I / (J - 1)]]; --  @DIVISION_CHECK:PASS
   begin
      pragma Assert (A (2, 2) = 2 and A (2, 3) = 1); --  @ASSERT:PASS
   end Nested;

   procedure Dynamic_Positional (First : Positive)
     with Pre => First <= 10
   is
      A : constant Vector (First .. First + 2) :=
        [0, for I in others => 10 / (I - First)]; --  @DIVISION_CHECK:PASS
   begin
      pragma Assert (A (First + 1) = 10); --  @ASSERT:PASS
   end Dynamic_Positional;

   procedure Dynamic_Nested (First : Positive)
     with Pre => First <= 10
   is
      A : constant Matrix (1 .. 2, First .. First + 2) :=
        [for I in 1 .. 2 =>
           [0, for J in others => I / (J - First)]]; --  @DIVISION_CHECK:PASS
   begin
      pragma Assert (A (2, First + 1) = 2); --  @ASSERT:PASS
   end Dynamic_Nested;

   procedure Shared_Bounds (First : Positive)
     with Pre => First <= 10
   is
      A : constant Matrix (1 .. 3, First .. First + 3) :=
        [[0, for J in others => 12 / (J - First)], --  @DIVISION_CHECK:PASS
         [0, 0, for J in others => 12 / (J - First - 1)], --  @DIVISION_CHECK:PASS
         [0, 0, 0, for J in others => 12 / (J - First - 2)]]; --  @DIVISION_CHECK:PASS
   begin
      pragma Assert (A (1, First + 3) = 4); --  @ASSERT:PASS
      pragma Assert (A (2, First + 3) = 6); --  @ASSERT:PASS
      pragma Assert (A (3, First + 3) = 12); --  @ASSERT:PASS
   end Shared_Bounds;

   procedure Unsafe is
      A : constant Vector (1 .. 3) :=
        [1 => 0, for I in others => 10 / (I - 2)]; --  @DIVISION_CHECK:FAIL
   begin
      null;
   end Unsafe;
begin
   null;
end Others_Choices;
