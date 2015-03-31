package Output_Port_05
  --# own out Output_State;
is
   procedure Write_To_Port(Output_Value : in Integer);
   --# global out Output_State;
   --# derives Output_State from Output_Value;
end Output_Port_05;
