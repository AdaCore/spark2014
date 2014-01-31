with Instruments,Surfaces,Degrees, Scale;
with AP.Altitude.Pitch.Rate;


use type Instruments.Feet,
  Instruments.Feetpermin,
  Degrees.Degreespersec,
  Surfaces.ControlAngle;


package body AP.Altitude.Pitch
  with Refined_State => (State => AP.Altitude.Pitch.Rate.Pitch_History)
is
   procedure Calc_Pitchrate(Pitch : in Instruments.Pitchangle;
                            Present_Pitchrate : out Degrees.Degreespersec)
     renames Rate.Calc_Pitchrate;

   subtype Floorfpm is Instruments.Feetpermin range -1000 .. 1000;
   subtype Degreespersec is Degrees.Degreespersec;

   function Target_ROC(Present_Altitude : Instruments.Feet;
                       Target_Altitude  : Instruments.Feet)
                      return Floorfpm
   is
      Result : Instruments.Feetpermin;
   begin
      Result := Instruments.Feetpermin( Integer(Target_Altitude -
                                                  Present_Altitude) / 10);
      if Result > Floorfpm'Last then
         Result := Floorfpm'Last;
      elsif Result <  Floorfpm'First then
         Result := Floorfpm'First;
      end if;
      return Result;
   end Target_ROC;

   function Target_Rate(Present_Altitude : Instruments.Feet;
                        Target_Altitude  : Instruments.Feet;
                        Climb_Rate : Instruments.Feetpermin)
                       return Degreespersec is
      Target_Climb_Rate : Floorfpm;
      Floor_Climb_Rate  : Floorfpm;
      Result            : Degreespersec;
   begin
      Target_Climb_Rate := Target_ROC(Present_Altitude,Target_Altitude);
      if Climb_Rate > Floorfpm'Last then
         Floor_Climb_Rate := Floorfpm'Last;
      elsif Climb_Rate < Floorfpm'First then
         Floor_Climb_Rate := Floorfpm'First;
      else
         Floor_Climb_Rate := Climb_Rate;
      end if;
      pragma Assert_And_Cut (Floor_Climb_Rate in Floorfpm
                               and Target_Climb_Rate in Floorfpm);
      Result := Degreespersec( (Target_Climb_Rate - Floor_Climb_Rate) / 12);
      if (Result > 10) then
         Result := 10;
      elsif (Result < -10) then
         Result := -10;
      end if;
      return Result;
   end Target_Rate;

   function Calc_Elevator_Move(Present_Pitchrate : Degreespersec;
                               Target_Pitchrate  : Degreespersec;
                               Mach              : Instruments.Machnumber)
                              return Surfaces.ControlAngle
   is
      Target_Angle : Surfaces.ControlAngle;
   begin
      Target_Angle := Scale.Scale_Movement(
        Mach    => Mach,
        Present => Scale.Scaledata(Present_Pitchrate / 2),
        Target  => Scale.Scaledata(Target_Pitchrate / 2),
        Max     => Surfaces.ControlAngle(30));

      return Target_Angle;
   end Calc_Elevator_Move;


   procedure Pitch_AP(Present_Altitude : in Instruments.Feet;
                      Target_Altitude  : in Instruments.Feet;
                      Mach             : in Instruments.Machnumber;
                      Climb_Rate       : in Instruments.Feetpermin;
                      The_Pitch        : in Instruments.Pitchangle)
     with Refined_Global  => (Output => Surfaces.Elevators,
                              In_Out => Rate.Pitch_History),
          Refined_Depends => (Rate.Pitch_History =>+ The_Pitch,
                              Surfaces.Elevators => (Climb_Rate,
                                                     Mach,
                                                     Present_Altitude,
                                                     Rate.Pitch_History,
                                                     Target_Altitude,
                                                     The_Pitch))
   is
      Present_Pitchrate : Degreespersec;
      Target_Pitchrate  : Degreespersec;
      Elevator_Movement : Surfaces.Controlangle;
   begin
      Calc_Pitchrate(The_Pitch, Present_Pitchrate);
      Target_Pitchrate := Target_Rate(Present_Altitude,
                                      Target_Altitude,
                                      Climb_Rate);
      Elevator_Movement := Calc_Elevator_Move(Present_Pitchrate,
                                              Target_Pitchrate,Mach);
      Surfaces.Move_Elevators(Elevator_Movement);
   end Pitch_AP;

end AP.Altitude.Pitch;
