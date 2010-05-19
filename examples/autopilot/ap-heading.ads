with AP.Controls, Instruments, Surfaces;
--# inherit AP.Controls, Instruments, Surfaces, Degrees, Scale;
private package AP.Heading
  --# own State;
  --# initializes State;
is
   procedure Maintain(Switch_Pressed   : in Controls.Switch;
                      Mach             : in Instruments.Machnumber;
                      Present_Heading  : in Instruments.Headdegree;
                      Target_Heading   : in Instruments.Headdegree;
                      Bank             : in Instruments.Bankangle;
                      Slip             : in Instruments.Slipangle);
   --# global in out State;
   --#           out Surfaces.Ailerons;
   --#           out Surfaces.Rudder;
   --# derives State
   --#          from *,
   --#               Switch_Pressed,
   --#               Bank,
   --#               Slip &
   --#         Surfaces.Ailerons
   --#          from State,
   --#               Switch_Pressed,
   --#               Mach,
   --#               Present_Heading,
   --#               Target_Heading,
   --#               Bank &
   --#         Surfaces.Rudder
   --#          from State,
   --#               Switch_Pressed,
   --#               Mach,
   --#               Slip
   --# ;

end AP.Heading;

