package Logging_In_Abstract with
  SPARK_Mode,
  Abstract_State => (State with External => (Async_Writers, Effective_Reads))
is
   procedure Get with
     Global  => (In_Out => State),
     Depends => (State =>+ null);

end Logging_In_Abstract;
