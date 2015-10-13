package Sensor with
  Abstract_State => (Power_Level with External => Async_Writers)
is

   procedure Read (T : out Float)
   with Global => (Input => Power_Level),
        Depends => (T => Power_Level);

end Sensor;
