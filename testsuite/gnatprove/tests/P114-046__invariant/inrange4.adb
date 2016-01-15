package body Inrange4
with SPARK_Mode
is

   -----------------------------------------------------------------------
   function InRange64(var: in Unsigned64; bottom: in Unsigned64; range_size: in Unsigned64)
                      return Boolean is
      Matched: Boolean := False;
      I: Unsigned64 := 0;
   begin
      for I in 0 .. range_size - 1 loop
         if (var = bottom + I) then
            Matched := True;
            exit;
         end if;
         pragma Loop_Invariant ((for all K in 0 .. I => var /= bottom + K)); --@LOOP_INVARANT:PASS
      end loop;
      return Matched;
   end InRange64;
   -----------------------------------------------------------------------

end Inrange4;

