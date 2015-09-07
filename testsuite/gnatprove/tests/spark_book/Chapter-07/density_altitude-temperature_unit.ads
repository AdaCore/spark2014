private package Density_Altitude.Temperature_Unit
   with Spark_Mode     => On,
        Abstract_State => (Temp_State
                              with External => Async_Writers,
                                   Part_Of  => Density_State)
is
   type Degrees is range -180 .. 180;

   procedure Read (Value : out Degrees)
     with Global  => (Input => Temp_State),
          Depends => (Value => Temp_State);

end Density_Altitude.Temperature_Unit;
