with TuningData;
limited with Timer, Display;

package User with
  SPARK_Mode,
  Abstract_State => Button_State
is

private
   protected type PT is
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
   end PT;
end User;
