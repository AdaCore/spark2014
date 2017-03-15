with State;
with Container;

procedure Main with SPARK_Mode is
begin
   pragma Assume (State.X);
   Container.Update_State_X_Via_Proxy; -- code in SPARK_Mode => Off changes State.X to False
   pragma Assert (State.X);            -- so this is assertion is false
end;
