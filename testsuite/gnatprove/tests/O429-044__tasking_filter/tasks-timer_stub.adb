with Ada.Real_Time; use Ada.Real_Time;

separate (Tasks)
task body Timer_Stub is
   Wakeup : Time := Clock;
begin
   delay until Clock;
   Wakeup := Wakeup + Seconds (1);
end Timer_Stub;
