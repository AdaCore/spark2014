package Array_Types with SPARK_Mode is

   type M is array (Positive range <>, Positive range <>) of Natural;

   function New_M (F1, L1, F2, L2 : Positive) return M is
     (F1 .. L1 => (F2 .. L2 => 0));

   A : M := New_M (1, 3, 2, 5);
   pragma Assert (A'First (1) = A'First (2)); --@ASSERT:FAIL

end Array_Types;
