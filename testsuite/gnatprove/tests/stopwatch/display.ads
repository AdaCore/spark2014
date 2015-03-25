with TuningData;

package Display with
  SPARK_Mode,
  Abstract_State =>
    ((Port_State with External => (Async_Readers, Effective_Writes)),
     State)
is
   procedure Initialize with
     Global  => (In_Out => State),
     Depends => (State =>+ null);

   procedure AddSecond with
     Global  => (In_Out => State),
     Depends => (State =>+ null);

private
   protected type PT with
     Interrupt_Priority => TuningData.DisplayPriority
   is

      -- add 1 second to stored time and send it to port
      procedure Increment with
        Global  => (Output => Port_State),
        Depends => ((Port_State, PT) => PT);

      -- clear time to 0 and send it to port;
      procedure Reset with
        Global  => (Output => Port_State),
        Depends => ((Port_State, PT) => null);

   private
      Counter : Natural := 0;
   end PT;
end Display;
