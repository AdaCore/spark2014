procedure Warn (Y : in out Integer) with
  SPARK_Mode
is
   X : Integer := 1;
begin
   X := 2;
   X := X + 3;
   pragma Assert (X = 5);
   Y := X;
end Warn;
