package body Counting with SPARK_Mode,
  Refined_State => (State => (Black_Counter, Red_Counter))
is
   Black_Counter, Red_Counter : Natural;

   procedure Reset_Black_Count with
     Refined_Global => (Output => Black_Counter) is
   begin
      Black_Counter := 0;
   end Reset_Black_Count;
   procedure Incr_Black_Count is
   begin
      Black_Counter := Black_Counter + 1;
   end Incr_Black_Count;
   function Get_Black_Count return Natural is (Black_Counter);

   procedure Reset_Red_Count with
     Refined_Global => (Output => Red_Counter) is
   begin
      Red_Counter := 0;
   end Reset_Red_Count;
   procedure Incr_Red_Count is
   begin
      Red_Counter := Red_Counter + 1;
   end Incr_Red_Count;
   function Get_Red_Count return Natural is (Red_Counter);

   procedure Reset_All is
   begin
      Reset_Black_Count;
      Reset_Red_Count;
   end Reset_All;
end Counting;
