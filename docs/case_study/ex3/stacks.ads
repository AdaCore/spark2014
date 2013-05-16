package Stacks is

   type Stack is limited private;

   function EmptyStack(S : in Stack) return Boolean;

   function FullStack(S : in Stack) return Boolean;

   procedure ClearStack(S :    out Stack);

   procedure Push(S : in out Stack; X : in Integer);

   procedure Pop(S : in out Stack; X : out Integer);

   procedure Top(S : in     Stack; X : out Integer);

private
   type Stack is new Integer;
end Stacks;
