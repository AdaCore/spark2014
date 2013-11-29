with System.Storage_Elements;

package Output_Port
  with SPARK_Mode
is
   Sensor : Integer
     with Volatile,
          Async_Readers,
          Address => System.Storage_Elements.To_Address (16#ACECAF0#);
end Output_Port;
