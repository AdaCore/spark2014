with AP.Heading.Roll, AP.Heading.Yaw;
package body AP.Heading
  with Refined_State => (State => (AP.Heading.Roll.State,
                                   AP.Heading.Yaw.State))
is
   procedure Maintain
     (Switch_Pressed  : in Controls.Switch;
      Mach            : in Instruments.Machnumber;
      Present_Heading : in Instruments.Headdegree;
      Target_Heading  : in Instruments.Headdegree;
      Bank            : in Instruments.Bankangle;
      Slip            : in Instruments.Slipangle)
     with Refined_Global  => (In_Out => (Surfaces.Ailerons,
                                         Surfaces.Rudder,
                                         Roll.State,
                                         Yaw.State)),
          Refined_Depends => (Roll.State        =>+ (Bank,
                                                     Switch_Pressed),
                              Surfaces.Ailerons =>+ (Bank,
                                                     Mach,
                                                     Present_Heading,
                                                     Roll.State,
                                                     Switch_Pressed,
                                                     Target_Heading),
                              Surfaces.Rudder   =>+ (Mach,
                                                     Slip,
                                                     Switch_Pressed,
                                                     Yaw.State),
                              Yaw.State         =>+ (Slip,
                                                     Switch_Pressed))
   is
   begin
      case Switch_Pressed is
         when Controls.On =>
            Roll.Roll_AP (Mach, Present_Heading, Target_Heading, Bank);
            Yaw.Yaw_AP (Mach, Slip);
         when Controls.Off =>
            null;
      end case;
   end Maintain;

end AP.Heading;
