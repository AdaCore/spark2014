procedure Test_Matrix (I : Integer) with SPARK_Mode is

   --  Test that 2-D arrays with FLB are slided correctly

   type Matrix is array (Positive range <>, Positive range <>) of Integer;
   type Matrix_1 is array (Positive range 1 .. <>, Positive range <>) of Integer;
   type Matrix_2 is array (Positive range <>, Positive range 1 .. <>) of Integer;
   type Matrix_3 is array (Positive range 1 .. <>, Positive range 1 .. <>) of Integer;

   A : Matrix := (2 => (2 => 1, 3 => 2), 3 => (2 => 3, 3 => 4));
   B : Matrix_1 := Matrix_1 (A);
   C : Matrix_2 := Matrix_2 (A);
   D : Matrix_3 := Matrix_3 (A);

begin
   --  Check the bounds

   if I = 1 then
      pragma Assert (B'Last (1) /= 2 or B'Last (2) /= 3); --@ASSERT:FAIL
   elsif I = 2 then
      pragma Assert (C'Last (1) /= 3 or C'Last (2) /= 2); --@ASSERT:FAIL
   elsif I = 3 then
      pragma Assert (D'Last (1) /= 2 or D'Last (2) /= 2); --@ASSERT:FAIL
   end if;

   --  Check the content

   if I = 4 then
      pragma Assert (B (1, 2) /= 1 or B (2, 3) /= 4); --@ASSERT:FAIL
   elsif I = 5 then
      pragma Assert (C (2, 1) /= 1 or C (3, 2) /= 4); --@ASSERT:FAIL
   elsif I = 6 then
      pragma Assert (D (1, 1) /= 1 or D (2, 2) /= 4); --@ASSERT:FAIL
   end if;
end Test_Matrix;
