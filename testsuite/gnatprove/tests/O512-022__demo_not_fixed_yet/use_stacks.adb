with Random_Numbers; use Random_Numbers;
with ASM_Stack;
with ADT_Stack;
with ADT_Stack.Child;
with  Generic_Stack;

package body Use_Stacks with SPARK_Mode is
   procedure Fill_ASM_Stack
   is
      V : Integer;
   begin
      ASM_Stack.Clear;
      loop
         Random_Numbers.Random (V);
         ASM_Stack.Push(V);
         exit when ASM_Stack.Is_Full;
      end loop;
   end Fill_ASM_Stack;

   procedure Fill_ADT_Stack
   is
      My_Stack : ADT_Stack.Stack;
      V : Integer;
   begin
      ADT_Stack.Clear(My_Stack);
      loop
         Random_Numbers.Random (V);
         ADT_Stack.Push(My_STack, V);
         exit when ADT_Stack.Is_Full(My_Stack);
      end loop;
   end Fill_ADT_Stack;

   procedure Fill_ADT_Stack_Child
   is
      My_Stack : ADT_Stack.Child.Child_Stack;
      V : Integer;
   begin
      ADT_Stack.Child.Clear (My_Stack);
      while (ADT_Stack.Child.Top_Identity (My_Stack) < 100) loop
         Random_Numbers.Random (V);
         ADT_Stack.Child.Push (My_STack, V);
      end loop;
   end Fill_ADT_Stack_Child;

   procedure Fill_Generic_Stack
   is
      package Stack_Int  is new Generic_Stack(Stack_Size => 100, Item => Integer);
   begin
      for I in 1 .. 100 loop -- insert automatically type in for-loop
         Stack_Int.Push (I);
      end loop;
   end Fill_Generic_Stack;

end Use_Stacks;
