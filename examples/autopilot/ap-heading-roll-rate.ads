with Degrees;
--# inherit Instruments,Degrees;
private package AP.Heading.Roll.Rate
  --# own Roll_History;
  --# initializes Roll_History;
is
   procedure Calc_Rollrate(Roll             : in  Instruments.Bankangle;
   			   Present_Rollrate : out Degrees.Degreespersec);
   --# global in out Roll_History;
   --# derives Present_Rollrate 
   --#          from Roll, 
   --#               Roll_History &
   --#         Roll_History
   --#          from *,
   --#               Roll
   --#   ;
   
end AP.Heading.Roll.Rate;

   
