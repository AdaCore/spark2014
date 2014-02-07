package Sensor
  with SPARK_Mode,
       Abstract_State => (State with External),
       Initializes    => State
is

   procedure Read (V : out Boolean)
     with Global => (Input => State),
          Depends => (V => State);

end Sensor;
