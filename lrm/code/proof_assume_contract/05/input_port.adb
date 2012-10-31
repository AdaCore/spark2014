
package body Input_Port
is

   Inputs : Integer;
   for Inputs'Address use 16#CAFE#;

   procedure Read_From_Port(Input_Value : out Integer)
   is
   begin
      --# assume Integer'First <= Inputs and Inputs <= Integer'Last;
      Input_Value := Inputs;
   end Read_From_Port;

end Input_Port;
