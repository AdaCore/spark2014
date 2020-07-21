package Stacks is

   type Element is new Integer;

   type Stack (Capacity : Positive) is private
     with Default_Initial_Condition => Empty (Stack);

   function Empty (This : Stack) return Boolean;

private

   type Content is array (Positive range <>) of Element
     with Relaxed_Initialization;

   type Stack (Capacity : Positive) is record
      Values : Content (1 .. Capacity);
      Top    : Natural := 0;
   end record  with
     Predicate => Top in 0 .. Capacity and then
       (for all K in 1 .. Top => Values (K)'Initialized);

   function Empty (This : Stack) return Boolean is (This.Top = 0);

end Stacks;
