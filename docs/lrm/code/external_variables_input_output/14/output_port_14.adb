package body Output_Port_14
   with Refined_State => (Output_State => Output_S)
is
   Output_S : Integer
      with Address => 16#CAFE#,
           Volatile;

   procedure Write_To_Port(Output_Value : in Integer)
      with Refined_Global  => (Output => Output_S),
           Refined_Depends => (Output_S => Output_Value)
   is
   begin
      Output_S := Output_Value;
   end Write_To_Port;
end Output_Port_14;
