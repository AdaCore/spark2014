with User, Timer, Display, Ada.Real_Time;

procedure Main with
  SPARK_Mode,
  Global  => (Input  => Ada.Real_Time.Clock_Time,
              In_Out => (User.Button_State,
                         Timer.Oper_State,
                         Display.State)),
  Depends => (User.Button_State =>+ null,
              Timer.Oper_State =>+ User.Button_State,
              Display.State    =>+ (Timer.Oper_State, User.Button_State),
              null             => Ada.Real_Time.Clock_Time),
  Priority => 10
is
begin
   null;
end Main;
