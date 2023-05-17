package Sensor
  with Abstract_State => (State with External),
       Initializes    => State
is

   procedure Read (V : out Boolean)
     with Global   => (Input => State),
          Depends  => (V => State),
          Always_Terminates;

end Sensor;
