package Stacks is

   type Stack is limited private;

   function EmptyStack(S : in Stack) return Boolean;

   function FullStack(S : in Stack) return Boolean;

   procedure ClearStack(S :    out Stack);
   --# derives S from ;

   procedure Push(S : in out Stack; X : in Integer);
   --# derives S from S, X;

   procedure Pop(S : in out Stack; X : out Integer);
   --# derives S from S &
   --#         X from S;

   procedure Top(S : in     Stack; X : out Integer);
   --# derives X from S;

private
--# hide Stacks
end Stacks;
