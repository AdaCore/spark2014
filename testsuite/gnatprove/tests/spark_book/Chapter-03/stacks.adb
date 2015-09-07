package body Stacks is

   procedure Clear (Stack : out Stack_Type) is
   begin
      Stack.Top := 0;
   end Clear;

   function Empty (Stack : in Stack_Type) return Boolean is
      (Stack.Top = 0);

   procedure Push (Item  : in     Integer;
                   Stack : in out Stack_Type) is
   begin
      Stack.Top := Stack.Top + 1;
      Stack.Items (Stack.Top) := Item;
   end Push;

   procedure Pop (Item  :    out Integer;
                  Stack : in out Stack_Type) is
   begin
      Item := Stack.Items (Stack.Top);
      Stack.Top := Stack.Top - 1;
   end Pop;

end Stacks;
