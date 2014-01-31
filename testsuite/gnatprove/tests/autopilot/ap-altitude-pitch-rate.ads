with Degrees, Instruments;

private package AP.Altitude.Pitch.Rate
  with Abstract_State => (Pitch_History
                            with Part_Of => AP.Altitude.Pitch.State),
       Initializes    => Pitch_History
is
   procedure Calc_Pitchrate(Pitch             : in  Instruments.Pitchangle;
			    Present_Pitchrate : out Degrees.Degreespersec)
     with Global  => (In_Out => Pitch_History),
          Depends => ((Pitch_History,
                       Present_Pitchrate) => (Pitch,
                                              Pitch_History));
end AP.Altitude.Pitch.Rate;
