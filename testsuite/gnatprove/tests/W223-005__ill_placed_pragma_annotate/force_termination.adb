with Infinite_Loop; use Infinite_Loop;

procedure Force_Termination
  with SPARK_Mode, Annotate => (GNATprove, Always_Return) is
   pragma Annotate (GNATprove, Always_Return, Loop_Indefinitely);
begin
   Loop_Indefinitely;
end Force_Termination;
