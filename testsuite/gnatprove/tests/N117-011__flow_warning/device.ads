package Device
  with SPARK_Mode,
       Abstract_State => (State with External => (Async_Readers,
                                                  Async_Writers)),
       Initializes    => State
is
   procedure Write (X : in Integer)
     with Global  => (In_Out => State),
         Depends => (State =>+ X);

   procedure ReadAck (OK : out Boolean)
     with Global  => (Input => State),
          Depends => (OK => State);

   function Last_Written return Integer
     with Global => State;

end Device;
