with Ada.Real_Time;

procedure Library_Level_Procedure
   with Global => Ada.Real_Time.Clock_Time
is
begin
   delay until Ada.Real_Time.Clock;
end;
