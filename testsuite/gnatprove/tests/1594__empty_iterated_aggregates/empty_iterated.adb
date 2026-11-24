procedure Empty_Iterated with SPARK_Mode is
   type Vector is array (Positive range <>) of Integer;
   type Matrix is array (Positive range <>, Positive range <>) of Integer;

   procedure Empty_Range is
      A : constant Vector := [for I in 2 .. 1 => I];
   begin
      pragma Assert (A'Length = 0); --  @ASSERT:PASS
      pragma Assert (False); --  @ASSERT:FAIL
   end Empty_Range;

   procedure Dynamic_Range (Last : Positive) is
      A : constant Vector := [for I in 2 .. Last => I];
   begin
      pragma Assert (A'Length = Last - 1); --  @ASSERT:PASS
      --  The aggregate must not imply that its iteration range is nonempty.
      pragma Assert (Last >= 2); --  @ASSERT:FAIL
   end Dynamic_Range;

   procedure Empty_Outer is
      A : constant Matrix :=
        [for I in 2 .. 1 => [for J in 1 .. 2 => I + J]];
   begin
      pragma Assert (A'Length (1) = 0); --  @ASSERT:PASS
      pragma Assert (False); --  @ASSERT:FAIL
   end Empty_Outer;

   procedure Empty_Inner is
      A : constant Matrix :=
        [for I in 1 .. 2 => [for J in 2 .. 1 => I + J]];
   begin
      pragma Assert (A'Length (1) = 2); --  @ASSERT:PASS
      pragma Assert (A'Length (2) = 0); --  @ASSERT:PASS
      pragma Assert (False); --  @ASSERT:FAIL
   end Empty_Inner;

   procedure Unsafe_Sibling (Divisor : Integer) is
      --  The first row's others association is empty. Its assumptions must
      --  not suppress checks in the second row.
      A : constant Matrix (1 .. 2, 1 .. 2) :=
        [for I in 1 .. 1 =>
           [for J in 1 .. 2 => I + J, for J in others => 0],
         for I in 2 .. 2 =>
           [for J in 1 .. 2 => I / Divisor]]; --  @DIVISION_CHECK:FAIL
   begin
      null;
   end Unsafe_Sibling;

   procedure Nonempty is
      A : constant Matrix :=
        [for I in 1 .. 2 => [for J in 1 .. 2 => 12 / (I + J)]]; --  @DIVISION_CHECK:PASS
   begin
      pragma Assert (A (1, 1) = 6 and A (2, 2) = 3); --  @ASSERT:PASS
   end Nonempty;
begin
   null;
end Empty_Iterated;
