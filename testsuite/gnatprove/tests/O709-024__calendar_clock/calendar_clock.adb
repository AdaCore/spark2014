with Ada.Calendar; use Ada.Calendar;

procedure Calendar_Clock is
   T1 : Time := Clock;
   T2 : Time := Clock;
begin
   pragma Assert (T1 = T2);  --  @ASSERT:FAIL
end Calendar_Clock;
