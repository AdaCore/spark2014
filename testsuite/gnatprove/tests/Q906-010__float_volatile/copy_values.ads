package Copy_Values
  with SPARK_Mode
is
   type F is new Float;
   Speed : F with Volatile, Async_Writers;
   Motor : F with Volatile, Async_Readers;

   procedure Adjust with
     Depends => (Motor =>+ Speed);

end Copy_Values;
