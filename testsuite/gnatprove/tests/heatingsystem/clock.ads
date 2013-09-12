
-- Clock
package Clock
--# own in Ticks : Times;
is pragma SPARK_Mode (On);
  subtype Times is Integer range 0 .. 86399;

  function PF_Read return Times;

  procedure Read (Time : out Times)
    with Post => (Time = PF_Read);
  --# global  in Ticks;
  --# derives Time from Ticks;
  --# post (Time = Ticks~);
  --  Once again "and (Ticks = Ticks'Tail (Ticks~));" has been omitted for simplicity.
  --
  -- Time contains the number of seconds since the controller was powered
  -- up and resets to zero every 24 hours.

end Clock;
