with Ada.Calendar;

procedure Delay_Cal1 is
   Now : constant Ada.Calendar.Time := Ada.Calendar.Clock;
   use type Ada.Calendar.Time;
   function Zero return Integer is (0);
   Up : constant Duration := Standard.Duration (1.0 / Zero);
begin
   null;
end;
