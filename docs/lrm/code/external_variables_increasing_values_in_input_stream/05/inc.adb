with System.Storage_Elements;
package body Inc
-- Cannot refine own variable Sensor as it has been given a concrete type.
is
   Sensor : Integer;
   for Sensor'Address use System.Storage_Elements.To_Address (16#DEADBEE0#);
   pragma Volatile (Sensor);

   procedure Read (V     : out Integer;
                   Valid : out Boolean)
   --# global in Sensor;
   --# post (Valid -> V = Sensor~) and
   --#      (Sensor = Sensor'Tail (Sensor~));
   is
      Tmp : Integer;
   begin
      Tmp := Sensor;
      if Tmp'Valid then
         V := Tmp;
         Valid := True;
         --# check Sensor = Sensor'Tail (Sensor~);
      else
         V := 0;
         Valid := False;
      end if;
   end Read;

   procedure Increases (Result : out Boolean;
                        Valid  : out Boolean)
   is
      A, B : Integer;
   begin
      Result := False;
      Read (A, Valid);
      if Valid then
         Read (B, Valid);
         if Valid then
            Result := B > A;
         end if;
      end if;
   end Increases;

end Inc;
