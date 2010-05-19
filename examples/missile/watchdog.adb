-- Watchdog timer implementation
--
-- $Log: watchdog.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/02/09 19:48:16  adi
-- Initial revision
--
--
with Clock;
use type Clock.Millisecond;
package body Watchdog
  --# own State is Last_Check, Last_Valid;
is
   -- Watchdog timeout at 750ms
   Max_Delay : constant Clock.Millisecond := 750;

   Last_Check : Clock.Millisecond := 0;
   Last_Valid : Boolean := False;

   -- The public procedure
   procedure Reset
     --# global    out Last_Check, Last_Valid;
     --#        in out Clock.Time;
     --# derives Last_Check, Last_Valid, Clock.Time
     --#    from Clock.Time;
   is
   begin
      Clock.Read(Last_Check,Last_Valid);
   end Reset;

   procedure Check_Timeout(V : out Timer_Check)
     --# global in     Last_Check, Last_Valid;
     --#        in out Clock.Time;
     --# derives Clock.Time from * &
     --#    V from Last_Check,Last_Valid,Clock.Time;
   is
      Valid : Boolean;
      T : Clock.Millisecond;
      Gap: Clock.Millisecond;
   begin
      Clock.Read(T,Valid);
      if (not Valid) or (not Last_Valid) then
         -- Watchdog not got valid data, assume invalid
         V := Invalid;
      else
         -- Both readings were valid, so compute the gap
         if T >= Last_Check then
            Gap := T - Last_Check;
         else
            -- T < Last_Check, implying clock wraparound
            Gap := (Clock.Millisecond'Last - Last_Check);
            Gap := Gap + T;
         end if;
         if Gap > Max_Delay then
            V := Timeout;
         else
            V := OK;
         end if;
      end if;
   end Check_Timeout;


end Watchdog;
