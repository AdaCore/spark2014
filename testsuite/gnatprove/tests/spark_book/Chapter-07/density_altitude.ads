package Density_Altitude
   with SPARK_Mode     => On,
        Abstract_State => (Density_State with External => Async_Writers)
is
   type Feet is range -5_0000 .. 100_000;

   procedure Read (Value : out Feet)
      with Global  => (Input => Density_State),
           Depends => (Value => Density_State);
end Density_Altitude;
