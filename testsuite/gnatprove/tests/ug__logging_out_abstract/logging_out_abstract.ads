package Logging_Out_Abstract with
  SPARK_Mode,
  Abstract_State => (State with External => (Async_Readers, Effective_Writes)),
  Initializes => State
is
   procedure Add_To_Total (Incr : in Integer) with
     Global  => (In_Out => State),
     Depends => (State =>+ Incr);

end Logging_Out_Abstract;
