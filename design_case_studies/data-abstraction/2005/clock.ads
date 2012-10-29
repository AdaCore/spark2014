
  -------------------------------------------------------------------

  package Clock
  --# own in Ticks;
  is

    subtype Times is integer range 0 .. 86399;

    procedure Read (Time : out Times);
    --# global  in Ticks;
    --# derives Time from Ticks;
    --
    -- Time contains the number of seconds since the controller was powered
    -- up and rests to zero every 24 hours.

  end Clock;
