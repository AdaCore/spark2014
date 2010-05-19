-- Time-related utilities implementation
--
-- $Log: clock_utils.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/02/09 20:35:18  adi
-- Initial revision
--
--
package body Clock_Utils is
   -- Wraparound time diff delta calculation
   function Delta_Time (Orig, Now : Clock.Millisecond)
                       return Clock.Millisecond
   is
      Gap : Clock.Millisecond;
   begin
      if Now >= Orig then
         Gap := Now - Orig;
      else
         -- Wraparound
         Gap := Clock.Millisecond'Last - Orig;
         Gap := Gap + Now;
      end if;
      return Gap;
   end Delta_Time;

   -- Add a delta to a time and deal with wraparound
   function Add_Delay(Orig, PlusDelta : Clock.Millisecond)
                     return Clock.Millisecond
   is
      Gap,Result : Clock.Millisecond;
   begin
      Gap := Clock.Millisecond'Last - Orig;
      if Gap >= PlusDelta then
         Result := Orig + PlusDelta;
      else
         Result := PlusDelta - Gap;
      end if;
      return Result;
   end Add_Delay;

   -- Subtract a delta from a time and deal with wraparound
   function Subtract_Delay(Orig, MinusDelta : Clock.Millisecond)
                          return Clock.Millisecond
   is
      Gap, Result : Clock.Millisecond;
   begin
      if Orig >= MinusDelta then
         Result := Orig - MinusDelta;
      else
         Gap := MinusDelta - Orig;
         Result := Clock.Millisecond'Last - Gap;
      end if;
      return Result;
   end Subtract_Delay;


end Clock_Utils;
