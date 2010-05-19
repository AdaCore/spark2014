--# inherit Surfaces, Instruments, Degrees, Scale;
private package AP.Heading.Roll
  --# own State;
  --# initializes State;
is
   procedure Roll_AP(Mach            : in Instruments.Machnumber;
		     Present_Heading : in Instruments.Headdegree;
		     Target_Heading  : in Instruments.Headdegree;
		     Bank            : in Instruments.Bankangle);
   --# global in out State;
   --#           out Surfaces.Ailerons;
   --# derives State 
   --#         from *,
   --#              Bank &
   --#         Surfaces.Ailerons
   --#         from State,
   --#              Present_Heading,
   --#              Target_Heading,
   --#              Mach,
   --#              Bank
   --#  ;
end AP.Heading.Roll;

   
