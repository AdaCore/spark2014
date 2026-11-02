procedure Positive_Zero with SPARK_Mode is
   X : Float := 0.0;
   N : Integer := -1;
   Y : Float;
begin
   --  Control case: the check must also fail for positive zero
   Y := X ** N; --@DIVISION_CHECK:FAIL
end Positive_Zero;
