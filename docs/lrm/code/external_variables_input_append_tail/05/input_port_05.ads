package Input_Port
  --# own in Inputs : Integer;
is
   procedure Read_From_Port(Input_Value : out Integer);
   --# global in Inputs;
   --# derives Input_Value from Inputs;
   --# post (Inputs~ = 0  -> (Input_Value = Inputs'Tail (Inputs~))) and
   --#      (Inputs~ /= 0 -> (Input_Value = Inputs~));

end Input_Port;
