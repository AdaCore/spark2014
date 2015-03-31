package body Input_Port_05
is

   Input_State : Integer;
   for Input_State'Address use
     System.Storage_Elements.To_Address (16#ACECAE0#);
   pragma Volatile (Input_State);

   procedure Read_From_Port(Input_Value : out Integer)
   is
   begin
      Input_Value := Input_State;
   end Read_From_Port;

end Input_Port_05;
