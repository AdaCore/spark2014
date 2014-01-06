with Lights;

procedure Main1
with
   Global => (Output => Lights.State),
   Depends => (Lights.State => null)
is
begin

   Lights.Init;

   loop
      Lights.Toggle;
   end loop;

end Main1;
