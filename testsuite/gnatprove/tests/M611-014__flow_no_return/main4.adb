with Lights;
with Sensor;

procedure Main4
with
   Global => (Input => Sensor.State,
              Output => Lights.State),
   Depends => (Lights.State => Sensor.State)
is

   procedure Control
   with
     Global => (Input  => Sensor.State,
                In_Out => Lights.State),
     Depends => (Lights.State =>+ Sensor.State),
     No_Return;

   procedure Shutdown
   with Global => (Output => Lights.State);

   procedure Control
   is
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

   procedure Shutdown
   is
   begin
      Lights.Explode;
   end Shutdown;

begin

   Lights.Init;

   Control;

   Shutdown;

end Main4;
