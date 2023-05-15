with Infinite_Loop; use Infinite_Loop;

procedure Force_Termination
  with SPARK_Mode, Always_Terminates is
begin
   Loop_Indefinitely;
end Force_Termination;
