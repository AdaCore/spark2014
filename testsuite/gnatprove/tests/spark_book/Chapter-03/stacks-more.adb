package body Stacks.More is
   function Peek (Stack : in Stack_Type) return Integer is
   begin
      return Stack.Items (Stack.Top);
   end Peek;
end Stacks.More;
