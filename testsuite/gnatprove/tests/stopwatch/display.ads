--  The stopwatch display can do only two things. Set the displayed
--  time to 0 or add 1 to it.

package Display with
  SPARK_Mode,
  Abstract_State => (LCD with Synchronous, External => Async_Readers)
is

   procedure Initialize with
     Global  => (Output => LCD),
     Depends => (LCD => null);

   procedure AddSecond with
     Global  => (In_Out => LCD),
     Depends => (LCD => LCD);

end Display;
