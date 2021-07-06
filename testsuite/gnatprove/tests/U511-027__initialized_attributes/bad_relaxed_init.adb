procedure Bad_Relaxed_Init with SPARK_Mode is
   X : Integer := 1;
begin
   pragma Assert (X'Initialized);
end Bad_Relaxed_Init;
