package body P is

   procedure Local_Proc (T : Table; A : Index)
     with Ghost
   is
   begin
      for B in T'Range loop
         pragma Loop_Invariant
           (for all K in T'First .. B =>
              (if A <= K then T(A) <= T(K)));
      end loop;
   end Local_Proc;

   procedure Lemma_Prove_Sorted_Alt (T : Table) is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Is_Sorted);
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Is_Sorted_Alt);
   begin
      for A in T'Range loop
         Local_Proc (T, A);
         pragma Loop_Invariant
           (for all J in T'First .. A =>
              (for all K in T'Range =>
                 (if J <= K then T(J) <= T(K))));
      end loop;
   end Lemma_Prove_Sorted_Alt;

end P;
