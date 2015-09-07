private package Density_Altitude.Pressure_Unit
   with Spark_Mode     => On,
        Abstract_State => (Press_State
                              with External => Async_Writers,
                                   Part_Of  => Density_State)
is
   type PSI is delta 0.0005 range  0.0 .. 30.0;

   procedure Read (Value : out PSI)
     with Global  => (Input => Press_State),
          Depends => (Value => Press_State);

end Density_Altitude.Pressure_Unit;
