package body integer_arrays with SPARK_Mode is

   procedure make_unique(arr: array_type) is
      result: array_type := (others => 0);
      result_index: Natural := 0;
   begin
      for i in arr'Range loop
         -- Does the output not contain this element?
         if (for all j in result'First .. result_index =>
               result(j) /= arr(i))
         then
            result_index := result_index + 1;
            pragma Assert(result_index in arr'Range);
            result(result_index) := arr(i);
         end if;

         pragma Loop_Invariant(result_index <= i);
         pragma Loop_Invariant(result_index <= result'First);  --  @LOOP_INVARIANT_PRESERV:FAIL
      end loop;
   end make_unique;

end integer_arrays;
