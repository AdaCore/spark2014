package Output_Port_14
  with SPARK_Mode,
       Abstract_State => (Output_State with External => Async_Readers)
is
   procedure Write_To_Port(Output_Value : in Integer)
     with Global  => (Output => Output_State),
          Depends => (Output_State => Output_Value);
end Output_Port_14;
