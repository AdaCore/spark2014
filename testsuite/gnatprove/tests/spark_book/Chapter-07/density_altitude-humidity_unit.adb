with System.Storage_Elements;
package body Density_Altitude.Humidity_Unit
   with Spark_Mode    => On,
        Refined_State => (Humid_State => Humid_Sensor)
is
   Humid_Sensor : Percent
     with Volatile        => True,
          Async_Writers   => True,
          Address         => System.Storage_Elements.To_Address (16#A1CAF0#);

   procedure Read (Value : out Percent)
      with Refined_Global  => (Input => Humid_Sensor),
           Refined_Depends => (Value => Humid_Sensor)
   is
   begin
      Value := Humid_Sensor;
   end Read;

end Density_Altitude.Humidity_Unit;
