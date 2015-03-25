with Timer, Display;

package body User with
  SPARK_Mode,
  Refined_State => (Button_State => Buttons)
is
   Buttons : PT;

   protected body PT is
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
   end PT;
end User;
