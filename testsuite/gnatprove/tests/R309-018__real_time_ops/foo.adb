with Ada.Real_Time; use Ada.Real_Time;
procedure Foo with Spark_mode is
   X : Ada.Real_Time.Time := Ada.Real_Time.Clock;
begin
   pragma Assert (X <= Ada.Real_Time.Time_Last);
end Foo;
