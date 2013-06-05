package body Input_Port_14
   with Refined_State => (Input_State => Input_S)
is
   Input_S : Integer
      with Address => 16#CAFE#,
           Volatile;

   procedure Read_From_Port(Input_Value : out Integer)
      with Refined_Global  => (Input => Input_S),
           Refined_Depends => (Input_Value => Input_S)
   is
   begin
      Input_Value := Input_S;
   end Read_From_Port;
end Input_Port_14;
