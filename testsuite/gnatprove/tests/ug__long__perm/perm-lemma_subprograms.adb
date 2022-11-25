package body Perm.Lemma_Subprograms with SPARK_Mode is

   procedure Occ_Eq (A, B : Nat_Array; LA, LB : Integer) with
     Subprogram_Variant => (Decreases => LA),
     Pre  => LA <= A'Last and then LB <= B'Last
     and then A (A'First .. LA) = B (B'First .. LB),
     Post => Occurrences (A, LA) = Occurrences (B, LB);

   procedure Occ_Eq (A, B : Nat_Array; LA, LB : Integer) is
   begin
      if LA < A'First then
         return;
      end if;

      Occ_Eq (A, B, LA - 1, LB - 1);
   end Occ_Eq;

   procedure Occ_Set_Rec
     (A : Nat_Array; I : Index; V : Natural; R : Nat_Array; L : Integer)
   with
     Subprogram_Variant => (Decreases => L),
     Pre  => I in A'Range and then Is_Set (A, I, V, R) and then L <= A'Last,
     Post =>
       (if V = A (I) or else I > L then Occurrences (R, L) = Occurrences (A, L)
        else Nb_Occurence (Occurrences (R, L), V) =
          Nb_Occurence (Occurrences (A, L), V) + 1
        and then Nb_Occurence (Occurrences (R, L), A (I)) =
          Nb_Occurence (Occurrences (A, L), A (I)) - 1
        and then
          (for all E of Union (Occurrences (R, L), Occurrences (A, L)) =>
             (if E not in V | A (I)
              then Nb_Occurence (Occurrences (R, L), E) =
                Nb_Occurence (Occurrences (A, L), E))));

   procedure Occ_Set_Rec
     (A : Nat_Array; I : Index; V : Natural; R : Nat_Array; L : Integer)
   is
   begin
      if L < A'First then
         return;
      end if;

      if I = L then
         Occ_Eq (A, R, L - 1, L - 1);
      else
         Occ_Set_Rec (A, I, V, R, L - 1);
      end if;
   end Occ_Set_Rec;

   procedure Occ_Set (A : Nat_Array; I : Index; V : Natural; R : Nat_Array)
   is
   begin
      Occ_Set_Rec (A, I, V, R, A'Last);
   end Occ_Set;

end Perm.Lemma_Subprograms;
