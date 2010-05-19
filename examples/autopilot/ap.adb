with Instruments,
     AP.Controls,
     AP.Altitude,
     AP.Heading;

package body AP
  --# own State is in AP.Controls.Master_Switch,
  --#              in AP.Controls.Altitude_Switch,
  --#              in AP.Controls.Heading_Switch,
  --#              AP.Altitude.State,
  --#              AP.Heading.State;
is
   procedure Control
     --# global in     Controls.Master_Switch,
     --#               Controls.Altitude_Switch,
     --#               Controls.Heading_Switch;
     --#        in out Altitude.State,
     --#               Heading.State;
     --#           out Surfaces.Elevators,
     --#               Surfaces.Ailerons,
     --#               Surfaces.Rudder;
     --#        in     Instruments.Altitude,
     --#               Instruments.Bank,
     --#               Instruments.Heading,
     --#               Instruments.Heading_Bug,
     --#               Instruments.Mach,
     --#               Instruments.Pitch,
     --#               Instruments.Rate_Of_Climb,
     --#               Instruments.Slip;
     --# derives Altitude.State
     --#          from *,
     --#               Controls.Master_Switch,
     --#               Controls.Altitude_Switch,
     --#               Instruments.Altitude,
     --#               Instruments.Pitch &
     --#         Heading.State
     --#          from *,
     --#               Controls.Master_Switch,
     --#               Controls.Heading_Switch,
     --#               Instruments.Bank,
     --#               Instruments.Slip &
     --#  Surfaces.Elevators
     --#          from Controls.Master_Switch,
     --#               Controls.Altitude_Switch,
     --#               Altitude.State,
     --#               Instruments.Altitude,
     --#               Instruments.Mach,
     --#               Instruments.Pitch,
     --#               Instruments.Rate_Of_Climb &
     --#  Surfaces.Ailerons
     --#          from Controls.Master_Switch,
     --#               Controls.Heading_Switch,
     --#               Heading.State,
     --#               Instruments.Bank,
     --#               Instruments.Heading,
     --#               Instruments.Heading_Bug,
     --#               Instruments.Mach &
     --#  Surfaces.Rudder
     --#          from Controls.Master_Switch,
     --#               Controls.Heading_Switch,
     --#               Heading.State,
     --#               Instruments.Mach,
     --#               Instruments.Slip
     --#  ;
   is
      Master_Switch, Altitude_Switch, Heading_Switch,
        Altitude_Selected, Heading_Selected : Controls.Switch;
      Present_Altitude : Instruments.Feet;
      Bank             : Instruments.Bankangle;
      Present_Heading  : Instruments.Headdegree;
      Target_Heading   : Instruments.Headdegree;
      Mach             : Instruments.Machnumber;
      Pitch            : Instruments.Pitchangle;
      Rate_Of_Climb    : Instruments.Feetpermin;
      Slip             : Instruments.Slipangle;
   begin
      Controls.Read_Master_Switch(Master_Switch);
      Controls.Read_Altitude_Switch(Altitude_Switch);
      Controls.Read_Heading_Switch(Heading_Switch);
      case Master_Switch is
         when Controls.On =>
            Altitude_Selected := Altitude_Switch;
            Heading_Selected := Heading_Switch;
         when Controls.Off =>
            Altitude_Selected := Controls.Off;
            Heading_Selected := Controls.Off;
      end case;
      Instruments.Read_Altimeter(Present_Altitude);
      Instruments.Read_Bank_Indicator(Bank);
      Instruments.Read_Compass(Present_Heading);
      Instruments.Read_Heading_Bug(Target_Heading);
      Instruments.Read_Mach_Indicator(Mach);
      Instruments.Read_Pitch_Indicator(Pitch);
      Instruments.Read_VSI(Rate_Of_Climb);
      Instruments.Read_Slip_Indicator(Slip);
      Altitude.Maintain(Altitude_Selected,Present_Altitude,Mach,Rate_Of_Climb,Pitch);
      Heading.Maintain(Heading_Selected,Mach,Present_Heading,Target_Heading,Bank,Slip);
   end Control;

end AP;


