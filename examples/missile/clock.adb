-- Clock implementation for simulation
--
-- $Log: clock.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/02/13 00:17:55  adi
-- Added Command separate
--
-- Revision 1.1  2003/02/08 17:38:45  adi
-- Initial revision
--
--
package body Clock
  --# own Time is Valid_Time, Ticks;
is
   Valid_Time : Boolean := False;
   Ticks : Millisecond := 0;

   -- Read the current time
   procedure Read(T : out Millisecond;
                  Valid : out Boolean)
     --# global in out Ticks;
     --#        in Valid_Time;
     --# derives
     --#      Valid from Valid_Time &
     --#      T, Ticks from Valid_Time, Ticks;
   is
   begin
      if Valid_Time then
         Valid := True;
         T := Ticks;
         -- Each read takes at least 1 millisecond
         if Ticks < Millisecond'Last then
            Ticks := Ticks + 1;
         else
            Ticks := 0;
         end if;
      else
         T := 0;
         Valid := False;
      end if;
   end Read;


   function Time_Valid return Boolean
     --# global in Valid_Time;
   is begin
      return Valid_Time;
   end Time_Valid;

   -- Reset the clock, making it valid
   procedure Reset
   --# global out Valid_Time, Ticks;
   --# derives Valid_Time, Ticks from;
   is
   begin
      Valid_Time := True;
      Ticks := 0;
   end Reset;

   -- Interface for simulation
   procedure Cycle(Plus : in Millisecond)
   --# global in out Ticks;
   --# derives Ticks from *, Plus;
   is begin
      if (Millisecond'Last - Plus) < Ticks then
         -- Wrap around
         Ticks := Plus - (Millisecond'Last - Ticks);
      else
         Ticks := Ticks + Plus;
      end if;
   end Cycle;

   procedure Command is separate;
end Clock;
