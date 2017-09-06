package Copy_Values
  with SPARK_Mode
is
   type F is delta 0.1 range -200.0 .. 200.0;

   procedure Adjust (X: F);
end Copy_Values;
