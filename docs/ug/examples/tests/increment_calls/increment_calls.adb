with Increment;
with Increment_Guarded;
with Increment_Full;

procedure Increment_Calls with
  SPARK_Mode
is
   X : Integer;
begin
   X := 0;
   Increment (X);
   Increment (X);

   X := 0;
   Increment_Guarded (X);
   Increment_Guarded (X);

   X := 0;
   Increment_Full (X);
   Increment_Full (X);
end Increment_Calls;
