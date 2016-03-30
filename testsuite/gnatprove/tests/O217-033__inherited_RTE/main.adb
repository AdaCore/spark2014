with Dispatch_In_Contract; use Dispatch_In_Contract;
procedure Main (Dummy : Integer) with SPARK_Mode is
   C1 : Root := (F1 => Integer'Last);
   C2 : Child := (F1 => Integer'Last, F2 => 1);
begin
   if Dummy = 0 then
      C1.Incr; --@PRECONDITION:FAIL
   elsif Dummy = 1 then
      C1.Incr2; --@PRECONDITION:FAIL
   elsif Dummy = 2 then
      C2.Incr; --@PRECONDITION:FAIL
   else
      C2.Incr2; --@PRECONDITION:PASS
   end if;
end Main;
