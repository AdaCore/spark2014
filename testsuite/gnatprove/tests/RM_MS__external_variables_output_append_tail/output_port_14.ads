package Output_Port_14
  with SPARK_Mode,
       Abstract_State => (Outputs with External => Async_Readers)
is
   procedure Write_To_Port(Output_Value : in Integer)
     with Global  => (Output => Outputs),
          Depends => (Outputs => Output_Value);
end Output_Port_14;
