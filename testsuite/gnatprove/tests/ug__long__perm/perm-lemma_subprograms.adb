package body Perm.Lemma_Subprograms with SPARK_Mode is

   procedure Occ_Eq (A, B : Nat_Array; E : Natural) with
     Pre  => A = B,
     Post => Occ (A, E) = Occ (B, E);

   procedure Occ_Eq (A, B : Nat_Array; E : Natural) is
      begin
      if A'Length = 0 then
         return;
      end if;

      if A (A'Last) = E then
         pragma Assert (B (B'Last) = E);
      else
         pragma Assert (B (B'Last) /= E);
      end if;

      Occ_Eq (Remove_Last (A), Remove_Last (B), E);
   end Occ_Eq;


   procedure Occ_Set (A : Nat_Array; I : Index; V, E : Natural; R : Nat_Array)
   is
      B : Nat_Array:= Remove_Last (A);
   begin
      if A'Length = 0 then
         return;
      end if;

      if I = A'Last then
         Occ_Eq (B, Remove_Last (R), E);
      else
         B (I) := V;
         Occ_Eq (Remove_Last (R), B, E);
         Occ_Set (Remove_Last (A), I, V, E, B);
      end if;
   end Occ_Set;

end Perm.Lemma_Subprograms;
