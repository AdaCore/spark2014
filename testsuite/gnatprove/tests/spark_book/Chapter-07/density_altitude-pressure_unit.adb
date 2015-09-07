with System.Storage_Elements;
package body Density_Altitude.Pressure_Unit
   with Spark_Mode    => On,
        Refined_State => (Press_State => Press_Sensor)
is
   Press_Sensor : PSI
     with Volatile        => True,
          Async_Writers   => True,
          Address         => System.Storage_Elements.To_Address (16#A1CAF8#);

   procedure Read (Value : out PSI)
      with Refined_Global  => (Input => Press_Sensor),
           Refined_Depends => (Value => Press_Sensor)
   is
   begin
      Value := Press_Sensor;
   end Read;

end Density_Altitude.Pressure_Unit;
