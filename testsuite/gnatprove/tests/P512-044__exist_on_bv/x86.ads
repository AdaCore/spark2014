with Interfaces;
use Interfaces;

package X86
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
     Post => (InRange64'Result = (for some N in Unsigned64 range 0 .. range_size => (var = (bottom + N))));
   -----------------------------------------------------------------------

   function RangesIntersect(var1: in Unsigned64; var1_range_size: in Unsigned64; var2: in Unsigned64; var2_range_size: in Unsigned64)
                                 return Boolean with Ghost,
     Pre => var1_range_size <= Unsigned64'Last - var2_range_size,
     Post => RangesIntersect'Result = (for some i in 0 .. var1_range_size =>
                                           (for some j in 0 .. var2_range_size =>
                                           (var1 + i) = (var2 + j)));

end X86;
