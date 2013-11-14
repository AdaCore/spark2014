with System.Storage_Elements;
package body Input_Port
is

   Inputs : Integer;
   for Inputs'Address use System.Storage_Elements.To_Address (16#CAFE0#);
   pragma Volatile (Inputs);

   procedure Read_From_Port(Input_Value : out Integer)
   is
   begin
      --# assume Inputs in Integer;
      Input_Value := Inputs;
   end Read_From_Port;

end Input_Port;
