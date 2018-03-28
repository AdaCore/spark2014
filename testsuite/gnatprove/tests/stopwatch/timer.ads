with TuningData;
limited with Ada.Synchronous_Task_Control, Ada.Real_Time, Display;

package Timer with
  SPARK_Mode,
  Abstract_State => (Timing_State,
                     (Oper_State with Synchronous,
                                      External => (Async_Readers,
                                                   Async_Writers)))
is

   -- These two procedures simply toggle suspension object Operate
   procedure StartClock with
     Global  => (In_Out => Oper_State),
     Depends => (Oper_State => null, null => Oper_State);

   procedure StopClock with
     Global  => (In_Out => Oper_State),
     Depends => (Oper_State => null, null => Oper_State);

end Timer;
