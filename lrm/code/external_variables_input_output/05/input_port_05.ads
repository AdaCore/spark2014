package Input_Port
  --# own in Inputs;
is
   procedure Read_From_Port(Input_Value : out Integer);
   --# global in Inputs;
   --# derives Input_Value from Inputs;

   function End_Of_Input return Boolean;
   --# global in Inputs;
end Input_Port;
