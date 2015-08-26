with Ada.Real_Time;

function Library_Level_Function return Boolean
   with Volatile_Function,
        Global => Ada.Real_Time.Clock_Time
is
begin
   delay until Ada.Real_Time.Clock;
   return True;
end;
