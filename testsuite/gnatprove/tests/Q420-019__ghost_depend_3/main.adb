pragma SPARK_Mode;

with State;

procedure Main with
  Global => (In_Out => State.State)
is
begin
   State.Test;
end Main;
