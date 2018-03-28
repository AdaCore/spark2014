with Ada.Synchronous_Task_Control, Ada.Real_Time, Display;
use type Ada.Real_Time.Time;

package body Timer with
  SPARK_Mode,
  Refined_State => (Timing_State => TimingLoop,
                    Oper_State   => Operate)
is

   Operate : Ada.Synchronous_Task_Control.Suspension_Object with Async_Readers,
                                                                 Async_Writers;

   task TimingLoop with
     Global   => (In_Out => (Operate, Display.State),
                  Input  => Ada.Real_Time.Clock_Time),
     Depends  => (Operate       => null,
                  Display.State => Display.State,
                  TimingLoop    => TimingLoop,
                  null          => (Ada.Real_Time.Clock_Time,
                                    Operate)),
     Priority => TuningData.TimerPriority;

   task body TimingLoop is
      Release_Time : Ada.Real_Time.Time;
      Period : constant Ada.Real_Time.Time_Span := TuningData.TimerPeriod;
   begin
      Display.Initialize; -- ensure we get 0 on the screen at start up
      loop
         -- wait until user allows clock to run
         -- calling procedure Suspend_Until_True which is Potentially_Blocking
         Ada.Synchronous_Task_Control.Suspend_Until_True (Operate);
         Ada.Synchronous_Task_Control.Set_True (Operate);
         -- once running, count the seconds
         -- calling Ada.Real_Time.Clock which is a Volatile_Function
         Release_Time := Ada.Real_Time.Clock;
         Release_Time := Release_Time + Period;
         delay until Release_Time;
         -- each time round, update the display
         Display.AddSecond;
      end loop;
   end TimingLoop;

   procedure StartClock with
     Refined_Global  => (In_Out => Operate),
     Refined_Depends => (Operate => null, null => Operate)
   is
   begin
      Ada.Synchronous_Task_Control.Set_True (Operate);
   end StartClock;

   procedure StopClock with
     Refined_Global  => (In_Out => Operate),
     Refined_Depends => (Operate => null, null => Operate)
   is
   begin
      Ada.Synchronous_Task_Control.Set_False (Operate);
   end StopClock;

end Timer;
