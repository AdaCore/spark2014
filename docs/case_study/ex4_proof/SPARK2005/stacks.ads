package Stacks is

   type Stack is limited private;

   Max_Count : constant Integer := 100;

   subtype Stack_Size is Natural range 0 .. Max_Count;

   --# function Size (S : in Stack) return Stack_Size;

   function EmptyStack(S : in Stack) return Boolean;
   --# return (Size(S) = 0);

   procedure ClearStack(S :    out Stack);
   --# post (Size(S) = 0);

   procedure Push(S : in out Stack; X : in Integer);
   --# pre  (Size (S) in 0 .. Max_Count-1);
   --# post (Size(S) = Size(S~) + 1);

   procedure Pop(S : in out Stack; X : out Integer);
   --# pre  (Size (S) in 1 .. Max_Count);
   --# post (Size(S) = Size(S~) - 1);

   procedure Top(S : in     Stack; X : out Integer);
   --# pre  (Size (S) in 1 .. Max_Count);

private
   subtype Count_T is Integer range 0 .. Max_Count;
   subtype Index_T is Count_T range 1 .. Max_Count;
   type Array_T is array (Index_T) of Integer;
   type Stack is record
      The_Top   : Count_T;
      The_Stack : Array_T;
   end record;
end Stacks;
