package body User with
  SPARK_Mode
is
   protected body Buttons is
      procedure StartClock
      is
      begin
         Timer.StartClock;
      end StartClock;

      procedure StopClock
      is
      begin
         Timer.StopClock;
      end StopClock;

      procedure ResetClock
      is
      begin
         Display.Initialize;
      end ResetClock;
   end Buttons;
end User;
