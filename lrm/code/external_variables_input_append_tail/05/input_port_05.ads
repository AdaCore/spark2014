package Input_Port
  --# own in Inputs : Integer;
is
   procedure Read_From_Port(Input_Value : out Integer);
   --# global in Inputs;
   --# derives Input_Value from Inputs;
   --# post Input_Value = Inputs~ and Inputs = Inputs'Tail (Inputs~);

end Input_Port;
