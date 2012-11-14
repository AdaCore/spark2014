with Input_Port_14, Output_Port_14, Stacks_14;
--  Approach for identifying main program is TBD.
procedure Copy_14
   with Global  => (Input  => Input_Port_14.Inputs,
                    Output => Output_Port_14.Outputs),
        Depends => (Output_Port_14.Outputs => Input_Port_14.Inputs)
is
   The_Stack   : Stacks_14.Stack;
   Value       : Integer;
   Done        : Boolean;
   Final_Value : constant Integer := 999;
begin
   Stacks_14.Clear(The_Stack);
   loop
      Input_Port_14.Read_From_Port(Value);
      Stacks_14.Push(The_Stack, Value);
      Done := Value = Final_Value;
      exit when Done;
   end loop;
   loop
      Stacks_14.Pop(The_Stack, Value);
      Output_Port_14.Write_To_Port(Value);
      exit when Stacks_14.Is_Empty(The_Stack);
   end loop;
end Copy_14;
