with Ada.Calendar;

procedure P2 with SPARK_Mode is
   Now : constant Ada.Calendar.Time := Ada.Calendar.Clock;
begin
   delay until Now;
end;
