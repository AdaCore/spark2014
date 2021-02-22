package body Assumptions with
  SPARK_Mode
is
   Clock_Ticks : Natural := 0;

   function Get_Tick return Natural is (Clock_Ticks);

   procedure Next_Tick is
   begin
      pragma Assume (Clock_Ticks < Natural'Last,
                     "Device uptime is short enough that Clock_Ticks is less than 1_000 always");
      Clock_Ticks := Clock_Ticks + 1;
   end Next_Tick;

end Assumptions;
