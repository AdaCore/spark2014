package Bad_Relaxed_Init with SPARK_Mode is
   type Priv is private with Relaxed_Initialization;

private
   type Priv is record
      F, G : Integer := 0;
   end record with
     Invariant => F <= G;
end Bad_Relaxed_Init;
