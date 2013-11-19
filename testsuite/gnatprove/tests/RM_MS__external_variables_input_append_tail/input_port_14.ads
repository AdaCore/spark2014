package Input_Port_14
  with SPARK_Mode,
       Abstract_State => (Inputs with External => Async_Writers)
is
   procedure Read_From_Port(Input_Value : out Integer)
     with Global  => Inputs,
          Depends => (Input_Value => Inputs);
end Input_Port_14;
