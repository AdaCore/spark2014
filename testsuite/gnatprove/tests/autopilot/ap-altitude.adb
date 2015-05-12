with AP.Altitude.Pitch;
package body AP.Altitude
  with Refined_State => (State => (Target_Altitude,
                                   Switch_Pressed_Before,
                                   AP.Altitude.Pitch.State))
is
   Target_Altitude : Instruments.Feet := 0;
   Switch_Pressed_Before : Controls.Switch := Controls.Off;

   procedure Maintain(Switch_Pressed   : in Controls.Switch;
		      Present_Altitude : in Instruments.Feet;
		      Mach             : in Instruments.Machnumber;
		      Climb_Rate       : in Instruments.Feetpermin;
		      The_Pitch        : in Instruments.Pitchangle)
     with Refined_Global  => (In_Out => (Surfaces.Elevators,
                                         Pitch.State,
                                         Switch_Pressed_Before,
                                         Target_Altitude)),
          Refined_Depends => (Pitch.State           =>+ (Switch_Pressed,
                                                         The_Pitch),
                              Surfaces.Elevators    =>+ (Climb_Rate,
                                                         Mach,
                                                         Pitch.State,
                                                         Present_Altitude,
                                                         Switch_Pressed,
                                                         Switch_Pressed_Before,
                                                         Target_Altitude,
                                                         The_Pitch),
                              Switch_Pressed_Before =>  Switch_Pressed,
                              Target_Altitude       =>+ (Present_Altitude,
                                                         Switch_Pressed,
                                                         Switch_Pressed_Before))
   is
   begin
      case Switch_Pressed is
   	 when Controls.On =>
	    case Switch_Pressed_Before is
	       when Controls.Off =>
		  Target_Altitude := Present_Altitude;
	       when Controls.On =>
		  null;
	    end case;
            Pitch.Pitch_AP(Present_Altitude,
                           Target_Altitude,Mach,
                           Climb_Rate,
                           The_Pitch);
	 when Controls.Off =>
   	    null;
      end case;
      Switch_Pressed_Before := Switch_Pressed;
   end Maintain;

end AP.Altitude;
