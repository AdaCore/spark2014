package body Input_Port
is

   Inputs : Integer;
   for Inputs'Address use
     System.Storage_Elements.To_Address (16#ACECAF0#);

   --# assert Inputs'Always_Valid;
   pragma Volatile (Inputs);

   procedure Read_From_Port(Input_Value : out Integer)
   is
   begin
      Input_Value := Inputs;
      if Input_Value = 0 then
         Input_Value := Inputs;
      end if;
   end Read_From_Port;

end Input_Port;
