-- Clock
package Clock
  with Abstract_State => (Ticks with External => Async_Writers)
is
  subtype Times is Integer range 0 .. 86399;

  procedure Read (Time : out Times)
    with Global  => Ticks,
         Depends => (Time => Ticks);
  -- Time contains the number of seconds since the controller was powered
  -- up and resets to zero every 24 hours.

end Clock;
