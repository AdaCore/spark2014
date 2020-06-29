procedure Relax_Init_Array_Op with SPARK_Mode is
   type My_Bool is new Boolean with Relaxed_Initialization;

   type Bool_Arr is array (Positive range <>) of My_Bool;

   X : Bool_Arr (1 .. 10) := (1 => False, others => True);
   Y : Bool_Arr (1 .. 10) := (1 => True, others => False);
begin
   pragma Assert (X'Initialized);
   pragma Assert ((X and Y) = (1 .. 10 => False));
   pragma Assert ((X or Y) = (1 .. 10 => True));
   pragma Assert ((not X) = Y);
end Relax_Init_Array_Op;
