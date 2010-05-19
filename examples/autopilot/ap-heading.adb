with AP.Heading.Roll, Ap.Heading.Yaw;
package body AP.Heading
--# own State is AP.Heading.Roll.State, AP.Heading.Yaw.State;
is
   procedure Maintain(Switch_Pressed   : in Controls.Switch;
                      Mach             : in Instruments.Machnumber;
                      Present_Heading  : in Instruments.Headdegree;
                      Target_Heading   : in Instruments.Headdegree;
                      Bank             : in Instruments.Bankangle;
                      Slip             : in Instruments.Slipangle)
     --# global in out Roll.State,
     --#               Yaw.State;
     --#           out Surfaces.Ailerons;
     --#           out Surfaces.Rudder;
     --# derives
     --#       Roll.State
     --#          from *,
     --#               Switch_Pressed,
     --#               Bank &
     --#       Yaw.State
     --#          from *,
     --#               Switch_Pressed,
     --#               Slip &
     --#       Surfaces.Ailerons
     --#          from Switch_Pressed,
     --#               Mach,
     --#               Present_Heading,
     --#               Target_Heading,
     --#               Bank,
     --#               Roll.State &
     --#         Surfaces.Rudder
     --#          from Switch_Pressed,
     --#               Mach,
     --#               Yaw.State,
     --#               Slip
     --# ;
   is
   begin
      case Switch_Pressed is
         when Controls.On =>
            Roll.Roll_AP(Mach,Present_Heading,Target_Heading,Bank);
            Yaw.Yaw_AP(Mach,Slip);
         when Controls.Off =>
            null;
      end case;
   end Maintain;


end AP.Heading;

