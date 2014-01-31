with Degrees, Instruments, Scale, Surfaces;

private package AP.Heading.Yaw
  with Abstract_State => (State with Part_Of => AP.Heading.State),
       Initializes    => State
is
   procedure Yaw_AP(Mach     : in Instruments.Machnumber;
		    Slip     : in Instruments.Slipangle)
     with Global  => (Output => Surfaces.Rudder,
                      In_Out => State),
          Depends => (State =>+ Slip,
                      Surfaces.Rudder => (Mach,
                                          Slip,
                                          State));
end AP.Heading.Yaw;
