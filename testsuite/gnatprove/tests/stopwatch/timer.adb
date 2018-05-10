with Ada.Real_Time, Display;
use type Ada.Real_Time.Time;

package body Timer with
  SPARK_Mode,
  Refined_State => (Control => Run_State)
is

   protected Run_State is
      pragma Priority (TuningData.UserPriority);

      procedure Start;

      procedure Stop;

      procedure Add_Time_If_Running
        with Global => (In_Out => Display.LCD);

      entry Wait_Until_Start;
   private
      Running : Boolean := False;
   end Run_State;

   protected body Run_State is
      procedure Start is
      begin
         Running := True;
      end Start;

      procedure Stop is
      begin
         Running := False;
      end Stop;

      procedure Add_Time_If_Running is
      begin
         if Running then
            Display.AddSecond;
         end if;
      end Add_Time_If_Running;

      pragma Warnings (Off, "statement has no effect",
                       Reason => "We use this just to block the task until" &
                                 " it is ready to run.");
      entry Wait_Until_Start when Running is
      begin
         null;
      end Wait_Until_Start;
      pragma Warnings (On, "statement has no effect");

   end Run_State;

   task body Timer with
     Refined_Depends => (Display.LCD => Run_State,
                         Run_State   => Run_State,
                         null        => Ada.Real_Time.Clock_Time)

   is
      Release_Time : Ada.Real_Time.Time := Ada.Real_Time.Clock;
      Period : Ada.Real_Time.Time_Span renames TuningData.TimerPeriod;
   begin
      Display.Initialize; -- ensure we get 0 on the screen at start up
      loop
         --  Wait until user allows clock to run...
         Run_State.Wait_Until_Start;

         --  Once running, count the seconds.
         Release_Time := Release_Time + Period;
         delay until Release_Time;

         --  Each time period, update the display. We check if we're
         --  still running to not *always* round up to the next second
         --  when we stop the clock.
         Run_State.Add_Time_If_Running;
      end loop;
   end Timer;

   procedure StartClock with
     Refined_Global  => (In_Out => Run_State),
     Refined_Depends => (Run_State => Run_State)
   is
   begin
      Run_State.Start;
   end StartClock;

   procedure StopClock with
     Refined_Global  => (In_Out => Run_State),
     Refined_Depends => (Run_State => Run_State)
   is
   begin
      Run_State.Stop;
   end StopClock;

end Timer;
