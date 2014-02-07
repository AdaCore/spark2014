with Lights;
with Sensor;

procedure Main3
  with SPARK_Mode,
       Global => (Input => Sensor.State,
                  Output => Lights.State),
       Depends => (Lights.State => Sensor.State)
is

   procedure Control with
      No_Return,
      Global => (Input  => Sensor.State,
                 In_Out => Lights.State),
      Depends => (Lights.State => +Sensor.State);

   procedure Control is
      Old : Boolean := False;
      V   : Boolean;
   begin
      loop
         Sensor.Read (V);
         if Old /= V then
            Old := V;
            Lights.Toggle;
         end if;
      end loop;
   end Control;

begin

   Lights.Init;
   Control;

end Main3;
