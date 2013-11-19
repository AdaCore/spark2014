with Input_Port_14,
     Output_Port_14,
     Stacks_14;
--  No need to specify that Copy_14 is a main program

procedure Copy_14
  with SPARK_Mode,
       Global  => (Input  => Input_Port_14.Input_State,
                   Output => Output_Port_14.Output_State),
       Depends => (Output_Port_14.Output_State => Input_Port_14.Input_State)
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
