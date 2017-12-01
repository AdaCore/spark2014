with TuningData;

package Display with
  SPARK_Mode,
  Abstract_State => (State with Synchronous, External => (Async_Readers,
                                                          Async_Writers,
                                                          Effective_Writes))
is
   procedure Initialize with
     Global  => (Output => State),
     Depends => (State => null);

   procedure AddSecond with
     Global  => (In_Out => State),
     Depends => (State => State);

end Display;
