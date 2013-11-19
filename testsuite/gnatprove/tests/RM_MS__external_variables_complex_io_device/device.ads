package Device
  with SPARK_Mode,
       Abstract_State => (State with External => (Async_Readers,
                                                  Async_Writers)),
       Initializes    => State
is
  procedure Write (X : in Integer)
    with Global  => (In_Out => State),
         Depends => (State =>+ X);
end Device;
