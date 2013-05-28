package Input_Port
   with Abstract_State => (State_Inputs with External, Input_Only)
is
   procedure Read_From_Port(Input_Value : out Integer)
      with Global  => (Input => State_Inputs),
           Depends => (Input_Value => State_Inputs);
end Input_Port;
