-- This is the Clock package from the Heating Controller Example from the
-- SPARK SWEWS Course changed to SPARK 2014.  It is included because it is
-- with'd by AdvanceButton.

  -------------------------------------------------------------------

package Clock
with
  Abnstract_State => (Ticks => Volatile_In)
is

   subtype Times is integer range 0 .. 86399;

   procedure Read (Time : out Times);
   with
     Global_In => Ticks,
     Derives => (Time => Ticks);
   -- Time contains the number of seconds since the controller was powered
   -- up and rests to zero every 24 hours.

end Clock;
