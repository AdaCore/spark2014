package body Inrange5
with SPARK_Mode
is

   function InRange64(var: in Unsigned64; bottom: in Unsigned64; range_size: in Unsigned64)
                      return Boolean is
   begin
      if range_size = 0 then
         return True;
      end if;
      if Unsigned64'Last - range_size + 1 >= bottom then
         return var in bottom .. bottom + range_size - 1;
      else
         return var in bottom .. Unsigned64'Last or else
           var in 0 .. range_size - (Unsigned64'Last - bottom) - 2;
      end if;
   end InRange64;

end Inrange5;
