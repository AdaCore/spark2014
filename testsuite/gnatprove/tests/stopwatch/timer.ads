with TuningData;
limited with Ada.Synchronous_Task_Control, Ada.Real_Time, Display;

package Timer with
  SPARK_Mode,
  Abstract_State => (Timing_State,
                     (Oper_State with External))
is

   -- These two procedures simply toggle suspension object Operate
   procedure StartClock with
     Global  => (Output => Oper_State),
     Depends => (Oper_State => null);

   procedure StopClock with
     Global  => (Output => Oper_State),
     Depends => (Oper_State => null);

end Timer;
