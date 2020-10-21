with Loop_Types; use Loop_Types;

procedure Update_Arr_Zero (A : in out Arr_T; Threshold : Component_T) with
  SPARK_Mode,
  Post => (for all J in A'Range => A(J) = (if A'Old(J) <= Threshold then 0 else A'Old(J)))
is
begin
   for J in A'Range loop
      if A(J) <= Threshold then
         A(J) := 0;
      end if;
      pragma Loop_Invariant (for all K in A'First .. J => A(K) = (if A'Loop_Entry(K) <= Threshold then 0 else A'Loop_Entry(K)));
      --  The following loop invariant is generated automatically by GNATprove:
      --  pragma Loop_Invariant (for all K in J + 1 .. A'Last => A(K) = A'Loop_Entry(K));
   end loop;
end Update_Arr_Zero;
