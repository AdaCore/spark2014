package Stacks is
-- Implements a simple stack of integers (with no safety features)
   type Stack_Type (Max_Size : Positive) is private
      with Default_Initial_Condition;

   procedure Clear (Stack : out Stack_Type);
   function Empty (Stack : in Stack_Type) return Boolean;
   procedure Push (Item  : in     Integer;
                   Stack : in out Stack_Type);
   procedure Pop (Item  :    out Integer;
                  Stack : in out Stack_Type);
private
   type Stack_Array is array (Positive range <>) of Integer;
   type Stack_Type (Max_Size : Positive) is
      record
         Top   : Natural := 0;  -- Initialize all stacks to empty
         Items : Stack_Array (1 .. Max_Size);
      end record;
end Stacks;
