--# inherit Surfaces, Instruments, Degrees, Scale;
private package AP.Altitude.Pitch
  --# own State;
  --# initializes State;
is
   procedure Pitch_AP(Present_Altitude : in Instruments.Feet;
		      Target_Altitude  : in Instruments.Feet;
		      Mach             : in Instruments.Machnumber;
		      Climb_Rate       : in Instruments.Feetpermin;
		      The_Pitch        : in Instruments.Pitchangle);
   --# global in out State;
   --#           out Surfaces.Elevators;
   --# derives State 
   --#         from *,
   --#              The_Pitch &
   --#         Surfaces.Elevators
   --#         from State,
   --#              Present_Altitude,
   --#              Target_Altitude,
   --#              Mach,
   --#              Climb_Rate,
   --#              The_Pitch
   --#  ;
end AP.Altitude.Pitch;

   
