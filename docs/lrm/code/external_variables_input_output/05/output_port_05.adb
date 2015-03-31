package body Output_Port_05
is

   Output_State : Integer;
   for Output_State'Address use
     System.Storage_Elements.To_Address (16#ACECAF0#);
   pragma Volatile (Output_State);

   procedure Write_To_Port(Output_Value : in Integer)
   is
   begin
      Output_State := Output_Value;
   end Write_To_Port;

end Output_Port_05;
