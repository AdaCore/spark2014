with Ada.Calendar;

procedure Delay_Cal is
   Now : constant Ada.Calendar.Time := Ada.Calendar.Clock;
begin
   delay until Now;
end;
