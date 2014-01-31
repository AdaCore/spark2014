with Degrees, Instruments;

private package AP.Heading.Roll.Rate
  with Abstract_State => (Roll_History with Part_Of => AP.Heading.Roll.State),
       Initializes    => Roll_History
is
   procedure Calc_Rollrate(Roll             : in  Instruments.Bankangle;
   			   Present_Rollrate : out Degrees.Degreespersec)
     with Global  => (In_Out => Roll_History),
          Depends => ((Present_Rollrate,
                       Roll_History) => (Roll,
                                         Roll_History));
end AP.Heading.Roll.Rate;
