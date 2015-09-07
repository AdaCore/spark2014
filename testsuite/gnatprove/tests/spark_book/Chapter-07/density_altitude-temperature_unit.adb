with System.Storage_Elements;
package body Density_Altitude.Temperature_Unit
   with Spark_Mode    => On,
        Refined_State => (Temp_State => Temp_Sensor)
is
   Temp_Sensor : Degrees
     with Volatile        => True,
          Async_Writers   => True,
          Address         => System.Storage_Elements.To_Address (16#A1CAF4#);


   procedure Read (Value : out Degrees)
      with Refined_Global  => (Input => Temp_Sensor),
           Refined_Depends => (Value => Temp_Sensor)
   is
   begin
      Value := Temp_Sensor;
   end Read;

end Density_Altitude.Temperature_Unit;
