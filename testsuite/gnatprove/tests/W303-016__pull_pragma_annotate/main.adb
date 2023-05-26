with Pulled; use Pulled;

procedure Main with SPARK_Mode, Annotate => (GNATprove, Always_Return) is
begin
   Terminating_Generic_Instance;
   Terminating_Instance;
   Terminating_Instance_2;
   A.B.C.Work;
end Main;
