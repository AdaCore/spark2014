--# inherit Surfaces, Instruments, Degrees, Scale;
private package AP.Heading.Yaw
  --# own State;
  --# initializes State;
is
   procedure Yaw_AP(Mach     : in Instruments.Machnumber;
		    Slip     : in Instruments.Slipangle);
   --# global in out State;
   --#           out Surfaces.Rudder;
   --# derives State 
   --#         from *,
   --#              Slip &
   --#         Surfaces.Rudder
   --#         from State,
   --#              Mach,
   --#              Slip
   --#  ;
end AP.Heading.Yaw;

   
