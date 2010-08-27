with Random_Numbers; use Random_Numbers;
with ASM_Stack;
with ADT_Stack;
with ADT_Stack.Child;

package body Use_Stacks
is

   procedure Fill_ASM_Stack
   is
   begin
      ASM_Stack.Clear;
      loop
         ASM_Stack.Push(Random_Numbers.Random);
         exit when ASM_Stack.Is_Full;
      end loop;
   end Fill_ASM_Stack;

   procedure Fill_ADT_Stack
   is
      My_Stack : ADT_Stack.Stack;
   begin
      ADT_Stack.Clear(My_Stack);
      loop
      ADT_Stack.Push(My_STack, Random_Numbers.Random);
         exit when ADT_Stack.Is_Full(My_Stack);
      end loop;
   end Fill_ADT_Stack;

   procedure Fill_ADT_Stack_Child
   is
      My_Stack : ADT_Stack.Child.Child_Stack;
   begin
      ADT_Stack.Child.Clear (My_Stack);
      while (ADT_Stack.Child.Top_Identity (My_Stack) < 100) loop
         ADT_Stack.Child.Push (My_STack, Random_Numbers.Random);
      end loop;
   end Fill_ADT_Stack_Child;

end Use_Stacks;
