with Instruments,
     AP.Controls,
     AP.Altitude,
     AP.Heading;

package body AP
  with Refined_State => (State => (AP.Controls.Master_Switch,
                                   AP.Controls.Altitude_Switch,
                                   AP.Controls.Heading_Switch,
                                   AP.Altitude.State,
                                   AP.Heading.State))
is
   procedure Control
     with Refined_Global  => (Input  => (Controls.Altitude_Switch,
                                         Controls.Heading_Switch,
                                         Controls.Master_Switch,
                                         Instruments.Altitude,
                                         Instruments.Bank,
                                         Instruments.Heading,
                                         Instruments.Heading_Bug,
                                         Instruments.Mach,
                                         Instruments.Pitch,
                                         Instruments.Rate_Of_Climb,
                                         Instruments.Slip),
                              In_Out => (Surfaces.Ailerons,
                                         Surfaces.Elevators,
                                         Surfaces.Rudder,
                                         Altitude.State,
                                         Heading.State)),
          Refined_Depends => (Altitude.State     =>+ (Controls.Altitude_Switch,
                                                      Controls.Master_Switch,
                                                      Instruments.Altitude,
                                                      Instruments.Pitch),
                              Heading.State      =>+ (Controls.Heading_Switch,
                                                      Controls.Master_Switch,
                                                      Instruments.Bank,
                                                      Instruments.Slip),
                              Surfaces.Ailerons  =>+ (Controls.Heading_Switch,
                                                      Controls.Master_Switch,
                                                      Heading.State,
                                                      Instruments.Bank,
                                                      Instruments.Heading,
                                                      Instruments.Heading_Bug,
                                                      Instruments.Mach),
                              Surfaces.Elevators =>+ (Altitude.State,
                                                      Controls.Altitude_Switch,
                                                      Controls.Master_Switch,
                                                      Instruments.Altitude,
                                                      Instruments.Mach,
                                                      Instruments.Pitch,
                                                      Instruments.Rate_Of_Climb),
                              Surfaces.Rudder    =>+ (Controls.Heading_Switch,
                                                      Controls.Master_Switch,
                                                      Heading.State,
                                                      Instruments.Mach,
                                                      Instruments.Slip))
   is
      Master_Switch, Altitude_Switch, Heading_Switch, Altitude_Selected,
      Heading_Selected : Controls.Switch;
      Present_Altitude : Instruments.Feet;
      Bank : Instruments.Bankangle;
      Present_Heading : Instruments.Headdegree;
      Target_Heading : Instruments.Headdegree;
      Mach : Instruments.Machnumber;
      Pitch : Instruments.Pitchangle;
      Rate_Of_Climb : Instruments.Feetpermin;
      Slip : Instruments.Slipangle;
   begin
      Controls.Read_Master_Switch (Master_Switch);
      Controls.Read_Altitude_Switch (Altitude_Switch);
      Controls.Read_Heading_Switch (Heading_Switch);
      case Master_Switch is
         when Controls.On =>
            Altitude_Selected := Altitude_Switch;
            Heading_Selected  := Heading_Switch;
         when Controls.Off =>
            Altitude_Selected := Controls.Off;
            Heading_Selected  := Controls.Off;
      end case;
      Instruments.Read_Altimeter (Present_Altitude);
      Instruments.Read_Bank_Indicator (Bank);
      Instruments.Read_Compass (Present_Heading);
      Instruments.Read_Heading_Bug (Target_Heading);
      Instruments.Read_Mach_Indicator (Mach);
      Instruments.Read_Pitch_Indicator (Pitch);
      Instruments.Read_VSI (Rate_Of_Climb);
      Instruments.Read_Slip_Indicator (Slip);
      Altitude.Maintain (Altitude_Selected,
                         Present_Altitude,
                         Mach,
                         Rate_Of_Climb,
                         Pitch);
      Heading.Maintain (Heading_Selected,
                        Mach,
                        Present_Heading,
                        Target_Heading,
                        Bank,
                        Slip);
   end Control;

end AP;
