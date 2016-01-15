package body Inrange2
with SPARK_Mode
is

   -----------------------------------------------------------------------
   function InRange64(var: in Unsigned64; bottom: in Unsigned64; range_size: in Unsigned64)
                      return Boolean is
      Matched: Boolean := False;
      I: Unsigned64 := 0;
   begin
      While_Loop:
      while ((I < range_size) and (not Matched)) loop
         if (var = bottom + I) then
            Matched := True;
            exit While_Loop;
         end if;
         I := I + 1;
         pragma Loop_Variant(Increases => I);
         pragma Loop_Invariant(Matched = (for some N in Unsigned64 range 0 ..  (I - 1) => (var = (bottom + N)))); --@ LOOP_INVARIANT:PASS
      end loop While_Loop;
      return Matched;
   end InRange64;
   -----------------------------------------------------------------------

end Inrange2;

