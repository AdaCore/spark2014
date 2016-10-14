with Ada.Real_Time;

procedure P1 with SPARK_Mode is
   Now : constant Ada.Real_Time.Time := Ada.Real_Time.Clock;
begin
   delay until Now;
end;
