with Use_Stacks;
with ASM_Stack;
with ADT_Stack;
with Ada.Text_IO;
procedure Main
is
   X, Y : Integer := 0;
   My_Stack : ADT_Stack.Stack;
   A        : Integer;
begin
   Use_Stacks.Fill_ADT_Stack;
   Use_Stacks.Fill_ASM_Stack;
   loop
      X := X + ASM_Stack.Pop;
      ADT_Stack.Pop(My_Stack, A);
      Y := Y + A;
      exit when ASM_Stack.Is_Empty and ADT_Stack.Is_Empty(My_Stack);
   end loop;

   if X < Y then
      Ada.Text_IO.Put_Line("ASM Stack won");
   elsif X > Y then
      Ada.Text_IO.Put_Line("ASM Stack won");
   else
      Ada.Text_IO.Put_Line("Game over match null");
   end if;

end Main;
