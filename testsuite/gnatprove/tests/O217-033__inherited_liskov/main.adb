with Dispatch_In_Contract; use Dispatch_In_Contract;
procedure Main with SPARK_Mode is
   C1 : Child := (F1 => 1, F2 => Integer'Last);
   C2 : Child := (F1 => 1, F2 => Integer'Last);
begin
   C1.Incr; -- Pre is failing for C1
   C2.Incr2; -- Pre should be failing for C2 ?
end Main;
