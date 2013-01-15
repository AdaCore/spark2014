package body Output_Port_14
is
   Output_State : Integer
      with Address => 16#CAFE#,
           Volatile;

   procedure Write_To_Port(Output_Value : in Integer)
   is
   begin
      Output_State := Output_Value;
   end Write_To_Port;
end Output_Port_14;
