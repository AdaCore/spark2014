with Loop_Types; use Loop_Types;

procedure Init_Arr_Zero (A : out Arr_T) with
  SPARK_Mode,
  Relaxed_Initialization => A,
  Post => A'Initialized and then (for all J in A'Range => A(J) = 0)
is
begin
   for J in A'Range loop
      A(J) := 0;
      pragma Loop_Invariant (for all K in A'First .. J => A(K)'Initialized);
      pragma Loop_Invariant (for all K in A'First .. J => A(K) = 0);
   end loop;
end Init_Arr_Zero;
