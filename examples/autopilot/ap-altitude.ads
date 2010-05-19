with AP.Controls, Instruments, Surfaces;
--# inherit AP.Controls, Instruments, Surfaces,Degrees,Scale;
private package AP.Altitude
  --# own State;
  --# initializes State;
is
   procedure Maintain(Switch_Pressed   : in Controls.Switch;
		      Present_Altitude : in Instruments.Feet;
		      Mach             : in Instruments.Machnumber;
		      Climb_Rate       : in Instruments.Feetpermin;
		      The_Pitch        : in Instruments.Pitchangle);
   --# global in out State;
   --#           out Surfaces.Elevators;
   --# derives State 
   --#          from *,
   --#               Switch_Pressed,
   --#               Present_Altitude,
   --#               The_Pitch &
   --#         Surfaces.Elevators
   --#          from State,
   --#               Switch_Pressed,
   --#               Present_Altitude,
   --#               Mach,
   --#               Climb_Rate,
   --#               The_Pitch
   --# ;
   
end AP.Altitude;
      
