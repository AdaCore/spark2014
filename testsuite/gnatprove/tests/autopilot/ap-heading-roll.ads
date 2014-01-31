with Degrees, Instruments, Scale, Surfaces;

private package AP.Heading.Roll
  with Abstract_State => (State with Part_Of => AP.Heading.State),
       Initializes    => State
is
   procedure Roll_AP(Mach            : in Instruments.Machnumber;
		     Present_Heading : in Instruments.Headdegree;
		     Target_Heading  : in Instruments.Headdegree;
		     Bank            : in Instruments.Bankangle)
     with Global  => (Output => Surfaces.Ailerons,
                      In_Out => State),
          Depends => (State =>+ Bank,
                      Surfaces.Ailerons => (Bank,
                                            Mach,
                                            Present_Heading,
                                            State,
                                            Target_Heading));
end AP.Heading.Roll;
