with TuningData;

package Display with
  SPARK_Mode,
  Abstract_State => (State with External => (Async_Readers, Effective_Writes))
is
   procedure Initialize with
     Global  => (In_Out => State),
     Depends => (State => State);

   procedure AddSecond with
     Global  => (Output => State),
     Depends => (State => null);

end Display;
