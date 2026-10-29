procedure Negative_Zero with SPARK_Mode is
   X : Float := Float'Copy_Sign (0.0, -1.0);
   N : Integer := -1;
   Y : Float;
begin
   --  Negative zero compares equal to zero in Ada. A negative exponent
   --  requires a division check for either sign of zero.
   Y := X ** N; --@DIVISION_CHECK:FAIL
end Negative_Zero;
