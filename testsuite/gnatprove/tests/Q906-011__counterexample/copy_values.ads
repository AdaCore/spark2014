package Copy_Values
  with SPARK_Mode
is
   type F is delta 0.1 range -200.0 .. 200.0;
   Speed : F with Volatile, Async_Writers;
   Motor : F with Volatile, Async_Readers;

   procedure Adjust with
     Depends => (Motor =>+ Speed);

end Copy_Values;
