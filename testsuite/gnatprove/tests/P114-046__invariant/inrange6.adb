package body Inrange6
with SPARK_Mode
is

   -----------------------------------------------------------------------
   function InRange64(var: in Unsigned64; bottom: in Unsigned64; range_size: in Unsigned64)
                      return Boolean is
      I: Unsigned64 := 0;
      Matched: Boolean;
   begin
      if (bottom <= Unsigned64'Last - Range_Size + 1) then
         Matched := (bottom <= var and var <= bottom + range_size - 1);
      else
         Matched := (bottom <= var and var <= Unsigned64'Last) or
           (var < range_size - (Unsigned64'Last - bottom) - 1);
      end if;
      return Matched;
   end InRange64;
   -----------------------------------------------------------------------

end Inrange6;
