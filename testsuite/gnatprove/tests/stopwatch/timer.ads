with Ada.Real_Time;

with TuningData;
with Display;

package Timer with
  SPARK_Mode,
  Abstract_State => (Control with Synchronous,
                                  External => (Async_Readers,
                                               Async_Writers))
is

   --  We note the resolution of this timing loop is 1 second. So if
   --  you stop the clock after .25 of a second has passed, and then
   --  start it again the display will only updated after an entire
   --  new second has passed.

   task Timer
     with Global => (In_Out => Control,
                     Input => Ada.Real_Time.Clock_Time,
                     Output => Display.LCD),
     Depends => (Display.LCD => Control,
                 Control => Control,
                 null => Ada.Real_Time.Clock_Time),
     Priority => TuningData.TimerPriority;

   procedure StartClock with
     Global  => (In_Out => Control),
     Depends => (Control => Control);

   procedure StopClock with
     Global  => (In_Out => Control),
     Depends => (Control => Control);

end Timer;
