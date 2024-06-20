with P; use P;
with SPARK.Cut_Operations; use SPARK.Cut_Operations;

procedure Q (T : Table; I, J : Index)
with
  Global => null,
  Pre => I in T'Range and then J in T'Range
is
   pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Is_Sorted_Alt);
begin
   if Is_Sorted (T)
     and then I < J
   then
      Lemma_Prove_Sorted_Alt (T);
      pragma Assert_And_Cut (Is_Sorted(T));
      pragma Assert (By (T(I) <= T(J), Is_Sorted_Alt(T)));
      pragma Assert (So (Is_Sorted_Alt(T), T(I) <= T(J)));
      pragma Assert (T(I) <= T(J));
   end if;
end Q;
