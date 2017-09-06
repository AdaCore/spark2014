package Copy_Values
  with SPARK_Mode
is
   Speed : Float with Volatile, Async_Writers;
   Motor : Float with Volatile, Async_Readers;

   procedure Adjust with
     Depends => (Motor =>+ Speed);

   Raw_Data : Float with Volatile, Async_Writers, Effective_Reads;
   Data     : Float with Volatile, Async_Readers, Effective_Writes;

   procedure Smooth with
     Depends => ((Raw_Data, Data) => Raw_Data);

end Copy_Values;
