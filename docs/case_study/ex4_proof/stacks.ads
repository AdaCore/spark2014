package Stacks is

   type Stack is private; -- had to remove 'limited' to allow use of 'Old
   Max_Count : constant Integer := 100;
   subtype Stack_Size is Natural range 0 .. Max_Count;

   -- Proof function that should not be called in code.
   function Size (S : in Stack) return Stack_Size;

   function EmptyStack(S : in Stack) return Boolean
      with Post => (EmptyStack'Result = (Size(S) = 0));

   function FullStack(S : in Stack) return Boolean;

   procedure ClearStack(S :    out Stack)
      with Post => (Size(S) = 0);

   procedure Push(S : in out Stack; X : in Integer)
      with pre => (Size (S) in 0 .. Max_Count - 1),
          post => (Size(S) = Size(S'Old) + 1);

   procedure Pop(S : in out Stack; X : out Integer)
     with pre => (Size (S) in 1 .. Max_Count),
          post => (Size(S) = Size(S'Old) - 1);

   procedure Top(S : in     Stack; X : out Integer)
     with pre => not EmptyStack (S);

private
   subtype Count_T is Integer range 0 .. Max_Count;
   subtype Index_T is Count_T range 1 .. Max_Count;
   type Array_T is array (Index_T) of Integer;
   type Stack is record
      The_Top   : Count_T;
      The_Stack : Array_T;
   end record;
end Stacks;
