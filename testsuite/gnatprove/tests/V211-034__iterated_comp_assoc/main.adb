procedure Main with SPARK_Mode is
   type Nat_Array is array (Positive range 1 .. 100) of Natural;
   type Arr_Array is array (Positive range 1 .. 100) of Nat_Array;

   M : Arr_Array with Relaxed_Initialization;
begin
   for I in M'Range loop
      M (I) := (for J in M (I)'Range => I + J);
      pragma Loop_Invariant
        (for all K in 1 .. I =>
           (for all J in 1 .. 100 => M (K) (J)'Initialized));
      pragma Loop_Invariant
        (for all K in 1 .. I =>
           (for all J in 1 .. 100 => M (K) (J) = K + J));
   end loop;
end Main;
