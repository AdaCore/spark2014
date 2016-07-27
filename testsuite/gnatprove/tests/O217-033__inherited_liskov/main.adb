with Dispatch_In_Contract; use Dispatch_In_Contract;
procedure Main (Dummy : Integer) with SPARK_Mode is
   C1 : Child := (F1 => 1, F2 => Integer'Last);
   C2 : Child := (F1 => 1, F2 => Integer'Last);
begin
   if Dummy = 1 then
      C1.Incr;  --  @PRECONDITION:FAIL
   else
      C2.Incr2; --  @PRECONDITION:FAIL
   end if;
end Main;
