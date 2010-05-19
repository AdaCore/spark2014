with Degrees;
--# inherit Instruments,Degrees;
private package AP.Heading.Yaw.Rate
  --# own Yaw_History;
  --# initializes Yaw_History;
is
   procedure Calc_Yawrate(Yaw             : in  Instruments.Slipangle;
   			  Present_Yawrate : out Degrees.Degreespersec);
   --# global in out Yaw_History;
   --# derives Present_Yawrate 
   --#          from Yaw, 
   --#               Yaw_History &
   --#         Yaw_History
   --#          from *,
   --#               Yaw
   --#   ;
   
end AP.Heading.Yaw.Rate;

   
