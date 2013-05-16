package Stacks is

   type Stack is limited private;

   function EmptyStack(S : in Stack) return Boolean;

   function FullStack(S : in Stack) return Boolean;

   procedure ClearStack(S :    out Stack);

   procedure Push(S : in out Stack; X : in Integer)
     with pre => not FullStack (S);

   procedure Pop(S : in out Stack; X : out Integer)
     with pre => not EmptyStack (S);

   procedure Top(S : in     Stack; X : out Integer)
     with pre => not EmptyStack (S);

private
   Max_Count : constant Integer := 100;
   subtype Count_T is Integer range 0 .. Max_Count;
   subtype Index_T is Count_T range 1 .. Max_Count;
   type Array_T is array (Index_T) of Integer;
   type Stack is record
      The_Top   : Count_T;
      The_Stack : Array_T;
   end record;
end Stacks;
