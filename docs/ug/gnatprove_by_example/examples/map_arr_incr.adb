with Loop_Types; use Loop_Types;

procedure Map_Arr_Incr (A : in out Arr_T) with
  SPARK_Mode,
  Pre  => (for all J in A'Range => A(J) /= Component_T'Last),
  Post => (for all J in A'Range => A(J) = A'Old(J) + 1)
is
begin
   for J in A'Range loop
      A(J) := A(J) + 1;
      pragma Loop_Invariant (for all K in A'First .. J => A(K) = A'Loop_Entry(K) + 1);
      --  The following loop invariant is generated automatically by GNATprove:
      --  pragma Loop_Invariant (for all K in J + 1 .. A'Last => A(K) = A'Loop_Entry(K));
   end loop;
end Map_Arr_Incr;
