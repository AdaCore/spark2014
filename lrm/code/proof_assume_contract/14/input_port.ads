package Input_Port
   with Abstract_State => ((Inputs with Volatile, Input))
is
   procedure Read_From_Port(Input_Value : out Integer)
      with Global  => (Input => Inputs),
           Depends => (Input_Value => Inputs);
end Input_Port;
