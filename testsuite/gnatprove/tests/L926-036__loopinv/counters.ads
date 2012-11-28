package Counters is
   type Change_Mode is
     (Increase,
      Increase_Then_Decrease,
      Same,
      Decrease,
      Decrease_Then_Increase);

   type Counter (Mode : Change_Mode; Ticks : Natural) is private;

   procedure Tick (C : in out Counter);
   --  Increment / decrement the counter depending on the scenario

   function Value (C : Counter) return Integer;
   --  Return the next value of the counter depending on the change scenario

private
   type Counter (Mode : Change_Mode; Ticks : Natural) is record
      C : Integer := 0;  --  count
      T : Natural := 0;  --  ticks
   end record;
end Counters;
