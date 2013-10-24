with System.Storage_Elements;

package Data is

   type Input_Value is (A, B, C, D, E);

   Sensor : Input_Value with Volatile;
   for Sensor'Address use System.Storage_Elements.To_Address (16#FFFF_FFFF#);

   Sensor_Valid : Boolean := False;

end Data;
