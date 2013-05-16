package body Stacks is

   function EmptyStack(S : in Stack) return Boolean
   is (S.The_Top = Count_T'First);

   function FullStack(S : in Stack) return Boolean
   is (S.The_Top = Count_T'Last);

   procedure ClearStack(S :    out Stack)
   is
   begin
      S.The_Stack := Array_T'(others => 0);
      S.The_Top   := Count_T'First;
   end ClearStack;

   procedure Push(S : in out Stack; X : in Integer) is
   begin
      S.The_Top := S.The_Top + 1;
      S.The_Stack (S.The_Top) := X;
   end Push;

   procedure Pop(S : in out Stack; X : out Integer) is
   begin
      X := S.The_Stack (S.The_Top);
      S.The_Top := S.The_Top - 1;
   end Pop;

   procedure Top(S : in     Stack; X : out Integer) is
   begin
      X := S.The_Stack (S.The_Top);
   end Top;

   function Size (S : in Stack) return Stack_Size is (S.The_Top);

end Stacks;
