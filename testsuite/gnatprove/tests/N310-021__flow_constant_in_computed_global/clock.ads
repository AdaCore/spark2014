-- Clock
package Clock
is
  subtype Times is Integer range 0 .. 86399;

  procedure Read (Time : out Times);
  -- Time contains the number of seconds since the controller was powered
  -- up and resets to zero every 24 hours.

end Clock;
