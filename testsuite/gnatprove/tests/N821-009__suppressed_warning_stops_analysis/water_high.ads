package Water_High
  with SPARK_Mode,
       Abstract_State => (Sensor with External => Async_Writers)
is
   procedure Is_Active (Active : out Boolean)
     with Global => Sensor;
end Water_High;
