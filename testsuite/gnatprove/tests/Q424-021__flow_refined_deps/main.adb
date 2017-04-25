pragma SPARK_Mode;

with State;
with Foo;

procedure Main with
  Global => (In_Out => State.State,
             Input => Foo.F)
is
begin
   State.Test;
end Main;
