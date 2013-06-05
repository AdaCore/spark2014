package body Input_Port
is

   Inputs : Integer;
   for Inputs'Address use 16#CAFE#;
   --# assert Inputs'Always_Valid;
   pragma Volatile (Inputs);

   procedure Read_From_Port(Input_Value : out Integer)
   is
   begin
      Input_Value := Inputs;
   end Read_From_Port;

end Input_Port;
