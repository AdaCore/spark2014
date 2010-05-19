with AP.Altitude.Pitch;
package body AP.Altitude
  --# own State is 
  --#   Target_Altitude, 
  --#   Switch_Pressed_Before,
  --#   AP.Altitude.Pitch.State;
is
   Target_Altitude : Instruments.Feet  
        := 0;
   Switch_Pressed_Before : Controls.Switch 
        := Controls.Off;
   
   procedure Maintain(Switch_Pressed   : in Controls.Switch;
		      Present_Altitude : in Instruments.Feet;
		      Mach             : in Instruments.Machnumber;
		      Climb_Rate       : in Instruments.Feetpermin;
		      The_Pitch        : in Instruments.Pitchangle)
   --# global in out Target_Altitude,
   --#               Switch_Pressed_Before,
   --#               Pitch.State;
   --#           out Surfaces.Elevators;
   --# derives  Target_Altitude
   --#          from *,
   --#               Switch_Pressed,
   --#               Switch_Pressed_Before,
   --#               Present_Altitude &
   --#          Pitch.State
   --#          from *,
   --#               Switch_Pressed,
   --#               The_Pitch &
   --#         Switch_Pressed_Before
   --#          from 
   --#               Switch_Pressed &
   --#         Surfaces.Elevators
   --#          from Switch_Pressed,
   --#               Switch_Pressed_Before,
   --#               Target_Altitude,
   --#               Present_Altitude,
   --#               Mach,
   --#               Climb_Rate,
   --#               The_Pitch,
   --#               Pitch.State
   --# ;
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
		  Pitch.Pitch_AP(Present_Altitude,Target_Altitude,Mach,Climb_Rate,The_Pitch);
	 when Controls.Off =>
   	    null;
      end case;
      Switch_Pressed_Before := Switch_Pressed;
   end Maintain;
   
   
end AP.Altitude;
      
