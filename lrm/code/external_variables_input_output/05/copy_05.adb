with Input_Port, Output_Port, Stacks;
--# inherit Input_Port, Output_Port, Stacks;
--# main_program;
procedure Copy
--# global in     Input_Port.Inputs;
--#        out    Output_Port.Outputs;
--# derives Output_Port.Outputs from Input_Port.Inputs;
is
   The_Stack   : Stacks.Stack;
   Value       : Integer;
   Done        : Boolean;
   Final_Value : constant Integer := 999;
begin
   Stacks.Clear(The_Stack);
   loop
      Input_Port.Read_From_Port(Value);
      Stacks.Push(The_Stack, Value);
      Done := Value = Final_Value;
      exit when Done;
   end loop;
   loop
      Stacks.Pop(The_Stack, Value);
      Output_Port.Write_To_Port(Value);
      exit when Stacks.Is_Empty(The_Stack);
   end loop;
end Copy;
