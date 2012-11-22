package body Input_Port_14
is
   Inputs : Integer
      with Address => 16#CAFE#,
           Volatile;

   procedure Read_From_Port(Input_Value : out Integer)
   is
   begin
      Input_Value := Inputs;
   end Read_From_Port;
end Input_Port_14;
