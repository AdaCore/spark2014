with System.Storage_Elements;

package body Input_Port
  with SPARK_Mode,
       Refined_State => (State_Inputs => Inputs)
is
   Inputs : Integer
     with Volatile,
          Async_Writers,
          Address => System.Storage_Elements.To_Address (16#CAFE0#);

   procedure Read_From_Port(Input_Value : out Integer)
     with Refined_Global  => (Input => Inputs),
          Refined_Depends => (Input_Value => Inputs)
   is
   begin
      Input_Value := Inputs;
      pragma Assume(Input_Value in Integer);
   end Read_From_Port;
end Input_Port;
