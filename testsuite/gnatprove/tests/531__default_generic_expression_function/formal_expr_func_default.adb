with Ada.Text_IO;  use Ada.Text_IO;

procedure Formal_Expr_Func_Default is

   generic
      type T is private;
      with function "*" (L, R : T) return T is <>;
      with function Copy_With_Square (Item : T) return T
             is (Item * Item); -- Expression default
   package Stacks is

      type Stack is limited private;

      procedure Push (S : in out Stack; X : T);

      function Pop (S : in out Stack) return T with Side_Effects;

      function Is_Empty (S : Stack) return Boolean;

   private

      subtype Stack_Range is Natural range 0 .. 100;

      type Stack_Array is array (Stack_Range range 1 .. Stack_Range'Last) of T;

      type Stack is record
         Top : Stack_Range := 0;
         Contents : Stack_Array;
      end record;

   end Stacks;

   package body Stacks is

      procedure Push (S : in out Stack; X : T) is
      begin
         S.Top := S.Top + 1;
         S.Contents (S.Top) := Copy_With_Square (X);
      end Push;

      function Pop (S : in out Stack) return T is
      begin
         S.Top := S.Top - 1;
         return Copy_With_Square (S.Contents (S.Top + 1));
      end Pop;

      function Is_Empty (S : Stack) return Boolean is
      begin
         return S.Top = 0;
      end Is_Empty;

   end Stacks;

   package Integer_Stacks is new Stacks (Integer);

   use Integer_Stacks;

   Int_Stack : Integer_Stacks.Stack;

begin
   for I in 1 .. 5 loop
      Push (Int_Stack, I);
   end loop;

   while not Is_Empty (Int_Stack) loop
      declare
	 Val : Integer;
      begin
	 Val := Pop (Int_Stack);
	 Put_Line (Val'Image);
      end;
   end loop;
end Formal_Expr_Func_Default;
