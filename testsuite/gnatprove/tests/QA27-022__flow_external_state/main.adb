with State;

procedure Main
with
   Post => State.Get >= 0
is
begin
   State.Update;
end Main;
