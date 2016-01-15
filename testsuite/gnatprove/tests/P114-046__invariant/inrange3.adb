package body Inrange3
with SPARK_Mode
is

   -----------------------------------------------------------------------
   function InRange64(var: in Unsigned64; bottom: in Unsigned64; range_size: in Unsigned64)
                      return Boolean is
      I: Unsigned64 := 0;
   begin
      While_Loop:
      while (I < range_size) loop
         pragma Loop_Variant(Increases => I);
         pragma Loop_Invariant --@ LOOP_INVARIANT:PASS
          (I in 0 .. range_size - 1 and
          ((I = 0) or else (for all N in Unsigned64 range 0 .. (I - 1) => (var /= (bottom + N)))));
         if (var = bottom + I) then
            return True;
         end if;
         I := I + 1;
      end loop While_Loop;
      return False;
   end InRange64;
   -----------------------------------------------------------------------

end Inrange3;
