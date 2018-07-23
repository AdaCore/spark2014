with Device_Interfaces; use Device_Interfaces;
with Device; use Device;

procedure Test_Device
  with SPARK_Mode => Off
is
   Success : Boolean;
begin
   Accel := 5.0; Giro := 10.0; Rotors := 15.0;
   Stabilize (Takeoff, Success);

   Accel := 5.0; Giro := 10.0; Rotors := Positive_Float'Last;
   Stabilize (Takeoff, Success);

end Test_Device;
