procedure Swap_Warn (X, Y : in out Integer) with
  SPARK_Mode
is
   Tmp_X : Integer;
   Tmp_Y : Integer;
begin
   Tmp_X := X;
   X := Tmp_Y;
   Tmp_Y := Y;
   Y := Tmp_X;
end Swap_Warn;
