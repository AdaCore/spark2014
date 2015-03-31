package body Output_Port
is

   Outputs : Integer;
   for Outputs'Address use System.Storage_Elements.To_Address (16#ACECAF10#);
   pragma Volatile (Outputs);

   procedure Write_To_Port(Output_Value : in Integer)
   is
   begin
      if Output_Value = -1 then
         Outputs := 0;
      end if;

      Outputs := Output_Value;
   end Write_To_Port;

end Output_Port;
