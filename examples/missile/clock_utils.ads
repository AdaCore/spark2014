-- Time-related utilities
--
-- $Log: clock_utils.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/02/09 20:35:11  adi
-- Initial revision
--
--
with Clock;
use type Clock.Millisecond;
--# inherit Clock;
package Clock_Utils is
   -- Wraparound time diff delta calculation
   function Delta_Time (Orig, Now : Clock.Millisecond)
                       return Clock.Millisecond;

   -- Add a delta to a time and deal with wraparound
   function Add_Delay(Orig, PlusDelta : Clock.Millisecond)
                     return Clock.Millisecond;

   -- Subtract a delta from a time and deal with wraparound
   function Subtract_Delay(Orig, MinusDelta : Clock.Millisecond)
                          return Clock.Millisecond;

end Clock_Utils;
