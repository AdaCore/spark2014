procedure Test_Loop_Array (B : Boolean) with SPARK_Mode is

   --  Test counterexample generation for indexes on one-dimensional arrays

   type Arr is array (1 .. 10) of Integer;

   A : Arr := (others => 0);
begin
   A (5) := 10;

   if B then
      for E of A loop
         pragma Assert (E = 0); -- @ASSERT:FAIL @COUNTEREXAMPLE
      end loop;
   else
      for I in A'Range loop
         pragma Assert (A (I) = 0); -- @ASSERT:FAIL @COUNTEREXAMPLE
      end loop;
   end if;
end;
