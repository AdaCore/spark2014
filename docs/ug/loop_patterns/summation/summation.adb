package body Summation
  with SPARK_Mode
is

   procedure Sum (A : in Ar; S: out Natural)
   is
   begin
      S := 0;

      for Idx in A'Range loop
         S := S + A (Idx);

         pragma Loop_Invariant (S <=  Max_Val * Idx);
      end loop;

   end Sum;

end Summation;
