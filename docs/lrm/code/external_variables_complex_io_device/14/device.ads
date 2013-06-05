package Device
   with Abstract_State => State,
        Initializes    => State
is
  procedure Write (X : in Integer)
     with Global  => (In_Out => State),
          Depends => (State =>+ X);
end Device;
