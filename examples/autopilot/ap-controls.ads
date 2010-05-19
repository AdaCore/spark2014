private package AP.Controls
  --# own in Master_Switch, 
  --#     in Altitude_Switch, 
  --#     in Heading_Switch;
is
   type Switch is (On, Off);
   
   procedure Read_Master_Switch(Position : out Switch);
   --# global in Master_Switch;
   --# derives Position from Master_Switch;
   
   procedure Read_Altitude_Switch(Position : out Switch);
   --# global in Altitude_Switch;
   --# derives Position from Altitude_Switch;
   
   procedure Read_Heading_Switch(Position : out Switch);
   --# global in Heading_Switch;
   --# derives Position from Heading_Switch;
   
end AP.Controls;
