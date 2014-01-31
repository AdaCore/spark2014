with Degrees, Instruments;

private package AP.Heading.Yaw.Rate
  with Abstract_State => (Yaw_History with Part_Of => AP.Heading.Yaw.State),
       Initializes    => Yaw_History
is
   procedure Calc_Yawrate(Yaw             : in  Instruments.Slipangle;
   			  Present_Yawrate : out Degrees.Degreespersec)
     with Global  => (In_Out => Yaw_History),
          Depends => ((Present_Yawrate,
                       Yaw_History) => (Yaw,
                                        Yaw_History));
end AP.Heading.Yaw.Rate;
