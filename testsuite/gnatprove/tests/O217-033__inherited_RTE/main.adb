with Dispatch_In_Contract; use Dispatch_In_Contract;
procedure Main with SPARK_Mode is
   C1 : Child := (F1 => Integer'Last, F2 => 1);
   C2 : Child := (F1 => Integer'Last, F2 => 1);
begin
   -- Like for Incr2, the precondition of Incr will never fail here.
   -- On the other hand, there is an overflow check in the body of Incr which
   -- will fail, like for Incr2.
   C1.Incr; --@PRECONDITION:PASS
   C2.Incr2;
end Main;
