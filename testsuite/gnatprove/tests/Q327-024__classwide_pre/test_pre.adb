with My_Types; use My_Types;
procedure Test_Pre with SPARK_Mode is
   X : My_Root := (F => Integer'Last);
begin
   Incr (X); --@PRECONDITION:FAIL
end Test_Pre;
