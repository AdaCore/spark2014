with Input_Port_05, Output_Port_05, Stacks_05;
--# inherit Input_Port_05, Output_Port_05, Stacks_05;
--# main_program;
procedure Copy_05
--# global in     Input_Port_05.Input_State;
--#        out    Output_Port_05.Output_State;
--# derives Output_Port_05.Output_State from Input_Port_05.Input_State;
is
   The_Stack   : Stacks_05.Stack;
   Value       : Integer;
   Done        : Boolean;
   Final_Value : constant Integer := 999;
begin
   Stacks_05.Clear(The_Stack);
   loop
      Input_Port_05.Read_From_Port(Value);
      Stacks_05.Push(The_Stack, Value);
      Done := Value = Final_Value;
      exit when Done;
   end loop;
   loop
      Stacks_05.Pop(The_Stack, Value);
      Output_Port_05.Write_To_Port(Value);
      exit when Stacks_05.Is_Empty(The_Stack);
   end loop;
end Copy_05;
