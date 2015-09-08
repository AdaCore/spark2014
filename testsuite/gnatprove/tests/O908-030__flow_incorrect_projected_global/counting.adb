package body Counting with
   Refined_State => (State => (Black_Counter, Red_Counter))
is
   Black_Counter, Red_Counter : Natural;

   procedure Reset_Black_Count is
   begin
      Black_Counter := 0;
   end Reset_Black_Count;

   procedure Reset_Red_Count is
   begin
      Red_Counter := 0;
   end Reset_Red_Count;
end Counting;
