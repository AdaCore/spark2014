with AP.Controls, Degrees, Instruments, Scale, Surfaces;

private package AP.Heading
  with Abstract_State => (State with Part_Of => AP.State),
       Initializes    => State
is
   procedure Maintain
     (Switch_Pressed  : in Controls.Switch;
      Mach            : in Instruments.Machnumber;
      Present_Heading : in Instruments.Headdegree;
      Target_Heading  : in Instruments.Headdegree;
      Bank            : in Instruments.Bankangle;
      Slip            : in Instruments.Slipangle)
     with Global  => (In_Out => (Surfaces.Ailerons,
                                 Surfaces.Rudder,
                                 State)),
          Depends => (State             =>+ (Bank,
                                             Slip,
                                             Switch_Pressed),
                      Surfaces.Ailerons =>+ (Bank,
                                             Mach,
                                             Present_Heading,
                                             State,
                                             Switch_Pressed,
                                             Target_Heading),
                      Surfaces.Rudder   =>+ (Mach,
                                             Slip,
                                             State,
                                             Switch_Pressed));
end AP.Heading;
