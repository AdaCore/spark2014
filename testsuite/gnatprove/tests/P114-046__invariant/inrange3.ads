with Interfaces;
use Interfaces;

package Inrange3
with SPARK_Mode
is
   subtype Unsigned64 is Interfaces.Unsigned_64;


   -----------------------------------------------------------------------
   -- InRange64 is designed to handle wrapping of Unsigned64 integers
   -- To test to see if val is between x and x+3, you would invoke
   -- InRange64(val, x, 4) which would check to see if val = x, x+1, x+2, or x+3
   -- This works even for the case where x = 2^64-1 and x+1 = 0.
   function InRange64(var: in Unsigned64; bottom: in Unsigned64; range_size: Unsigned64)
                      return Boolean with Ghost,
     Pre => ((range_size >= 2) and (range_size <= 16#FFFF#)),
     Post => (InRange64'Result = (for some N in Unsigned64 range 0 .. (range_size - 1) => (var = (bottom + N)))); --@ POSTCONDITION:PASS
   -----------------------------------------------------------------------

end Inrange3;
