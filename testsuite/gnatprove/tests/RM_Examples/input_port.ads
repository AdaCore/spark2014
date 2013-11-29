with System.Storage_Elements;

package Input_Port
  with SPARK_Mode
is
   Sensor : Integer
     with Volatile,
          Async_Writers,
          Address => System.Storage_Elements.To_Address (16#ACECAF0#);
end Input_Port;
