-- Clock
package Clock
  with Abstract_State => (Ticks with External => Async_Writers)
is
  subtype Times is Integer range 0 .. 86399;

  function PF_Read return Times
    with Global => Ticks;

  procedure Read (Time : out Times)
    with Global  => (In_Out => Ticks),
         Depends => ((Ticks,
                      Time) => Ticks),
         Post    => Time = PF_Read;
  -- Time contains the number of seconds since the controller was powered
  -- up and resets to zero every 24 hours.

end Clock;
