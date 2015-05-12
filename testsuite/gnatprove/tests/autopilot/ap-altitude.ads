with AP.Controls, Degrees, Instruments, Scale, Surfaces;

private package AP.Altitude
  with Abstract_State => (State with Part_Of => AP.State),
       Initializes    => State
is
   procedure Maintain(Switch_Pressed   : in Controls.Switch;
		      Present_Altitude : in Instruments.Feet;
		      Mach             : in Instruments.Machnumber;
		      Climb_Rate       : in Instruments.Feetpermin;
		      The_Pitch        : in Instruments.Pitchangle)
     with Global  => (In_Out => (Surfaces.Elevators,
                                 State)),
          Depends => (State              =>+ (Present_Altitude,
                                              Switch_Pressed,
                                              The_Pitch),
                      Surfaces.Elevators =>+ (Climb_Rate,
                                              Mach,
                                              Present_Altitude,
                                              State,
                                              Switch_Pressed,
                                              The_Pitch));
end AP.Altitude;
