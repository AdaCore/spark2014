with Lights;

procedure Main2
with
   Global => (Output => Lights.State),
   Depends => (Lights.State => null)
is
begin

   Lights.Init;

   Lights.Toggle;

   Lights.Explode;

end Main2;
