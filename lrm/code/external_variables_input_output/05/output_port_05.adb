package body Output_Port
is

   Outputs : Integer;
   for Outputs'Address use 16#CAFE#;

   procedure Write_To_Port(Output_Value : in Integer)
   is
   begin
      Outputs := Output_Value;
   end Write_To_Port;

end Output_Port;
