with System.Storage_Elements;

package body Output_Port_14
  with SPARK_Mode,
       Refined_State => (Outputs => Output_Port)
is
   Output_Port : Integer
     with Volatile,
          Async_Readers,
          Address => System.Storage_Elements.To_Address (16#ACECAF10#);

   -- This is a simple subprogram that always updates the Output_Shadow with
   -- the single value which is written to the output port.
   procedure Write_It (Output_Value : in Integer; Output_Shadow : out Integer)
     with Global  => (Output => Output_Port),
          Depends => ((Output_Port, Output_Shadow) => Output_Value),
          Post    => Output_Shadow = Output_Value
   is
   begin
      Output_Shadow := Output_Value;
      Output_Port := Output_Shadow;
   end Write_It;


   procedure Write_To_Port(Output_Value : in Integer)
     with Refined_Global  => (Output => Output_Port),
          Refined_Depends => (Output_Port => Output_Value)
   is
      Out_1, Out_2 : Integer;
   begin
      if Output_Value = -1 then
         Write_It (0, Out_1);
         Write_It (Output_Value, Out_2);
      else
         Write_It (Output_Value, Out_1);
         Out_2 := Out_1;  -- Avoids flow error.
      end if;

      pragma Assert (if Output_Value = -1 then
                        Out_1 = 0 and Out_2 = Output_Value
                     else
                        Out_1 = Output_Value);
   end Write_To_Port;
end Output_Port_14;
