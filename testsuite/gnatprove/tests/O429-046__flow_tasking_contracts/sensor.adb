with System.Storage_Elements;

package body Sensor with
  Refined_State => (Power_Level => (Sensor_1, Sensor_2))
is

   Sensor_1 : Float with
     Volatile,
     Async_Writers,
     Address => System.Storage_Elements.To_Address (16#FFFF_EEEE#);

   Sensor_2 : Float with
     Volatile,
     Async_Writers,
     Address => System.Storage_Elements.To_Address (16#FFFF_FFFF#);

   procedure Read (T : out Float)
   with Refined_Global => (Sensor_1, Sensor_2),
        Refined_Depends => (T => (Sensor_1, Sensor_2))
   is
      A : constant Float := Sensor_1;
      B : constant Float := Sensor_2;
   begin
      T := Float'Max (A, B);
   end Read;

end Sensor;
