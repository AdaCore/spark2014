package body Copy_Values
  with SPARK_Mode
is
   procedure Adjust (X: F) is
   begin
      pragma Assert (X < 5.0);
   end Adjust;

end Copy_Values;
