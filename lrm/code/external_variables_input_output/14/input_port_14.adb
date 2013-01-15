package body Input_Port_14
is
   Input_State : Integer
      with Address => 16#CAFE#,
           Volatile;

   procedure Read_From_Port(Input_Value : out Integer)
   is
   begin
      Input_Value := Input_State;
   end Read_From_Port;
end Input_Port_14;
