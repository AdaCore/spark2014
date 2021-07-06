procedure Relaxed_Init with SPARK_Mode is
   X : Integer := 1 with Relaxed_Initialization;
begin
   pragma Assert (X'Initialized);
end Relaxed_Init;
