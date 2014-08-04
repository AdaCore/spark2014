package Perm.Lemma_Subprograms with SPARK_Mode is

   procedure Occ_Eq (A, B : Nat_Array; E : Natural) with
     Pre     => A = B,
     Post    => Occ (A, E) = Occ (B, E);

   function Set (A : Nat_Array; I : Index; V : Natural) return Nat_Array with
     Pre  => I in A'Range,
     Post => Set'Result'First = A'First and then Set'Result'Last = A'Last
     and then Set'Result (I) = V
     and then (for all J in A'Range =>
                 (if I /= J then Set'Result (J) = A (J)));

   procedure Occ_Set (A : Nat_Array; I : Index; V, E : Natural) with
     Pre     => I in A'Range,
     Post    =>
       (if V = A (I) then Occ (Set (A, I, V), E) = Occ (A, E)
        elsif V = E then Occ (Set (A, I, V), E) = Occ (A, E) + 1
        elsif A (I) = E then Occ (Set (A, I, V), E) = Occ (A, E) - 1
        else Occ (Set (A, I, V), E) = Occ (A, E));

end Perm.Lemma_Subprograms;
