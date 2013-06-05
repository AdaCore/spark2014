package Output_Port_14
   with Abstract_State => (Output_State with External, Output_Only)
is
   procedure Write_To_Port(Output_Value : in Integer)
      with Global  => (Output => Output_State),
           Depends => (Output_State => Output_Value);
end Output_Port_14;
