package Counting with SPARK_Mode,
  Abstract_State => State
is
   procedure Reset_Black_Count with
     Global => (In_Out => State),
     Post   => Get_Black_Count = 0;
   procedure Incr_Black_Count with
     Pre  => Get_Black_Count < Integer'Last,
     Post => Get_Black_Count = Get_Black_Count'Old + 1;
   function Get_Black_Count return Natural;

   procedure Reset_Red_Count with
     Global => (In_Out => State),
     Post   => Get_Red_Count = 0;
   procedure Incr_Red_Count with
     Pre  => Get_Red_Count < Integer'Last,
     Post => Get_Red_Count = Get_Red_Count'Old + 1;
   function Get_Red_Count return Natural;

   procedure Reset_All with
     Global => (Output => State);
end Counting;
