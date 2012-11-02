package Input_Port
with
   Abstract_State => (Volatile => (Input => Inputs))
is
   procedure Read_From_Port(Input_Value : out Integer)
   with
      Global  => (Input => Inputs),
      Depends => (Input_Value => Inputs);
      
end Input_Port;
