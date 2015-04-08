with Timer, Display;

package body User with
  SPARK_Mode,
  Refined_State => (Button_State => Buttons)
is
   protected Buttons is
      pragma Interrupt_Priority (TuningData.UserPriority);

      procedure StartClock with
        Global  => (Output => Timer.Oper_State),
        Depends => (Timer.Oper_State => null),
        Attach_Handler => 1;

      procedure StopClock with
        Global  => (Output => Timer.Oper_State),
        Depends => (Timer.Oper_State => null),
        Attach_Handler => 2;

      procedure ResetClock with
        Global  => (In_Out => Display.State),
        Depends => (Display.State =>+ null),
        Attach_Handler => 3;
   end Buttons;

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
