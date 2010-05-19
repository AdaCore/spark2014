with Degrees;
--# inherit Instruments,Degrees;
private package AP.Altitude.Pitch.Rate
  --# own Pitch_History;
  --# initializes Pitch_History;
is
   procedure Calc_Pitchrate(Pitch             : in  Instruments.Pitchangle;
			    Present_Pitchrate : out Degrees.Degreespersec);
   --# global in out Pitch_History;
   --# derives Present_Pitchrate 
   --#        from Pitch,
   --#             Pitch_History &
   --#  Pitch_History
   --#        from *,
   --#             Pitch
   --#  ;
   
end AP.Altitude.Pitch.Rate;
