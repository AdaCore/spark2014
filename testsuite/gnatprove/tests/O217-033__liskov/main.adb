with Dispatch_In_Contract; use Dispatch_In_Contract;
procedure Main with SPARK_Mode is
   C1 : Grand_Child := (F1 => 1, F2 => Integer'Last);
begin
   Incr (Root'Class (C1));
end Main;
