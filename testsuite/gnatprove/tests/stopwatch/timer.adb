with Ada.Synchronous_Task_Control, Ada.Real_Time, Display;
use type Ada.Real_Time.Time;

package body Timer with
  SPARK_Mode,
  Refined_State => (Oper_State => Operate, Timing_State => TimingLoop)
is

   Operate    : Ada.Synchronous_Task_Control.Suspension_Object;
   TimingLoop : TT;

   procedure StartClock
   is
   begin
      Ada.Synchronous_Task_Control.Set_True (Operate);
   end StartClock;

   procedure StopClock
   is
   begin
      Ada.Synchronous_Task_Control.Set_False (Operate);
   end StopClock;

   task body TT is
      Release_Time : Ada.Real_Time.Time;
      Period : constant Ada.Real_Time.Time_Span :=
        TuningData.TimerPeriod;
   begin
      Display.Initialize; -- ensure we get 0 on the screen at start up
      loop
         -- wait until user allows clock to run
         Ada.Synchronous_Task_Control.Suspend_Until_True (Operate);
         Ada.Synchronous_Task_Control.Set_True (Operate);
         -- once running, count the seconds
         Release_Time := Ada.Real_Time.Clock;
         Release_Time := Release_Time + Period;
         delay until Release_Time;
         -- each time round, update the display
         Display.AddSecond;
      end loop;
   end TT;
end Timer;
