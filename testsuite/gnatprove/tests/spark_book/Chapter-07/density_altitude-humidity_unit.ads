private package Density_Altitude.Humidity_Unit
   with Spark_Mode     => On,
        Abstract_State => (Humid_State
                              with External => Async_Writers,
                                   Part_Of  => Density_State)
is
   type Percent is range  0 .. 100;

   procedure Read (Value : out Percent)
     with Global  => (Input => Humid_State),
          Depends => (Value => Humid_State);

end Density_Altitude.Humidity_Unit;
