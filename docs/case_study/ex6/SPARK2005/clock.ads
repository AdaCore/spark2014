
-- Clock
package Clock
--# own in Ticks : Times;
is
  subtype Times is Integer range 0 .. 86399;

  procedure Read (Time : out Times);
  --# global  in Ticks;
  --# derives Time from Ticks;
  --# post (Time = Ticks~);
  --  Once again "and (Ticks = Ticks'Tail (Ticks~));" has been omitted for simplicity.
  --
  -- Time contains the number of seconds since the controller was powered
  -- up and resets to zero every 24 hours.

end Clock;
