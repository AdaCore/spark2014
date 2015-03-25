with TuningData;
limited with Ada.Synchronous_Task_Control, Ada.Real_Time, Display;

package Timer with
  SPARK_Mode,
  Abstract_State => (Oper_State, Timing_State)
is

   -- These two procedure simply toggle suspension object Operate
   procedure StartClock with
     Global  => (Output => Oper_State),
     Depends => (Oper_State => null);

   procedure StopClock with
     Global  => (Output => Oper_State),
     Depends => (Oper_State => null);

private
   task type TT with
     Global  => (Output => Oper_State,
                 In_Out => Display.State,
                 Input  => Ada.Real_Time.Clock_Time),
     Depends => (Oper_State    => null,
                 Display.State =>+ null,
                 null          => Ada.Real_Time.Clock_Time),
     Priority => TuningData.TimerPriority
   is
   end TT;
end Timer;
