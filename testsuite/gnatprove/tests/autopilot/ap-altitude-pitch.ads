with Degrees, Instruments, Scale, Surfaces;

private package AP.Altitude.Pitch
  with Abstract_State => (State with Part_Of => AP.Altitude.State),
       Initializes    => State
is
   procedure Pitch_AP(Present_Altitude : in Instruments.Feet;
		      Target_Altitude  : in Instruments.Feet;
		      Mach             : in Instruments.Machnumber;
		      Climb_Rate       : in Instruments.Feetpermin;
		      The_Pitch        : in Instruments.Pitchangle)
     with Global  => (Output => Surfaces.Elevators,
                      In_Out => State),
          Depends => (State =>+ The_Pitch,
                      Surfaces.Elevators => (Climb_Rate,
                                             Mach,
                                             Present_Altitude,
                                             State,
                                             Target_Altitude,
                                             The_Pitch));
end AP.Altitude.Pitch;
