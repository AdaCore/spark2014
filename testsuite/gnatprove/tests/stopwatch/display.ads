with TuningData;

package Display with
  SPARK_Mode,
  Abstract_State => (State with Synchronous, External => (Async_Readers,
                                                          Async_Writers))
is
   procedure Initialize with
     Global  => (In_Out => State),
     Depends => (State => State);

   procedure AddSecond with
     Global  => (In_Out => State),
     Depends => (State => State);

end Display;
