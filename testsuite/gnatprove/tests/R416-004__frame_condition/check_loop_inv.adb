procedure Check_Loop_Inv with SPARK_Mode is
   type nat_array is array (Positive range <>) of Natural;
   V : Integer := 20;
   A : nat_array := (1 .. 100 => 0);
   function Get_V return Integer is (V);
begin
   for I in 11 .. Get_V loop
      pragma Loop_Invariant (True);
      V := 0;
      A (I) := 1;
   end loop;
   pragma Assert (A (1 .. 10) = (1 .. 10 => 0)); --@ASSERT:PASS
   pragma Assert (A (21 .. 100) = (21 .. 100 => 0)); --@ASSERT:PASS
   pragma Assert (A (11 .. 20) = (11 .. 20 => 1)); --@ASSERT:FAIL

   for I in A (21 .. 30)'Range loop
      pragma Loop_Invariant (True);
      A (21 .. 30) (I) := 2;
   end loop;
   pragma Assert (A (1 .. 10) = (1 .. 10 => 0)); --@ASSERT:PASS
   pragma Assert (A (31 .. 100) = (31 .. 100 => 0)); --@ASSERT:PASS
   pragma Assert (A (11 .. 20) = (11 .. 20 => 1)); --@ASSERT:PASS
   pragma Assert (A (21 .. 30) = (21 .. 30 => 2)); --@ASSERT:FAIL

   for I in A (31 .. 40)'Range loop
      pragma Loop_Invariant (True);
      A (31 .. 40) (I .. I) := (I => 3);
   end loop;
   pragma Assert (A (1 .. 10) = (1 .. 10 => 0)); --@ASSERT:PASS
   pragma Assert (A (41 .. 100) = (41 .. 100 => 0)); --@ASSERT:PASS
   pragma Assert (A (11 .. 20) = (11 .. 20 => 1)); --@ASSERT:PASS
   pragma Assert (A (21 .. 30) = (21 .. 30 => 2)); --@ASSERT:PASS
   pragma Assert (A (31 .. 40) = (31 .. 40 => 3)); --@ASSERT:FAIL
end Check_Loop_Inv;
