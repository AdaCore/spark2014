with System.Storage_Elements;

package body Water_High
  with SPARK_Mode,
       Refined_State => (Sensor => High_Sensor_Port)
is
   type Sensor_Values is range 0 .. 200;

   Active_Value : constant Sensor_Values := 200;

   High_Sensor_Port : Sensor_Values
     with Volatile,
          Async_Writers,
          Address => System.Storage_Elements.To_Address (16#FFFF_FFFF#);

   procedure Is_Active (Active : out Boolean)
     with Refined_Global => High_Sensor_Port
   is
      Raw_Value : Sensor_Values;
   begin
      Raw_Value := High_Sensor_Port;
      pragma Warnings (Off, "attribute Valid is assumed to return True");
      if Raw_Value'Valid then
         Active := Raw_Value = Active_Value;
      else
         Active := True;  -- "safe" value
      end if;
   end Is_Active;

end Water_High;
