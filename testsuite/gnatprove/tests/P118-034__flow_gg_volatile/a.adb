with System.Storage_Elements;

package body A with
  Refined_State => (State     => Cache,
                    Ext_State => (Sensor, Actuator))
is
   Cache : Integer := 0;

   Sensor : Integer
     with Volatile,
          Async_Writers,
          Address => System.Storage_Elements.To_Address (16#DEADBEEF0#);

   Actuator : Boolean
     with Volatile,
          Async_Readers,
          Address => System.Storage_Elements.To_Address (16#C0FFEE#);

   procedure Test_01
   is
      Tmp : constant Integer := Sensor;
   begin
      if Tmp > Cache then
         Actuator := False;
      end if;
   end Test_01;

   procedure Test_02
   is
      Tmp : constant Integer := Sensor;
   begin
      Actuator := Tmp > 0;
   end Test_02;

begin
   declare
      Tmp : constant Integer := Sensor;
   begin
      Actuator := Tmp = 0;
   end;
end A;
