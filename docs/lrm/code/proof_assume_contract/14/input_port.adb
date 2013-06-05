package body Input_Port
   with Refined_State => (State_Inputs => Inputs)
is
   Inputs : Integer;
   for Inputs'Address use 16#CAFE#;
   pragma Volatile (Inputs);

   procedure Read_From_Port(Input_Value : out Integer)
      with Refined_Global  => (Input => Inputs),
           Refined_Depends => (Input_Value => Inputs)
   is
   begin
      pragma Assume(Inputs in Integer);
      Input_Value := Inputs;
   end Read_From_Port;
end Input_Port;
