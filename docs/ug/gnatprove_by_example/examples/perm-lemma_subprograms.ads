package Perm.Lemma_Subprograms with SPARK_Mode, Ghost is

   function Is_Set (A : Nat_Array; I : Index; V : Natural; R : Nat_Array)
                    return Boolean
   is (R'First = A'First and then R'Last = A'Last
       and then R (I) = V
       and then (for all J in A'Range =>
                   (if I /= J then R (J) = A (J)))) with
     Pre  => I in A'Range;

   procedure Occ_Set (A : Nat_Array; I : Index; V, E : Natural; R : Nat_Array)
   with
     Pre     => I in A'Range and then Is_Set (A, I, V, R),
     Post    =>
       (if V = A (I) then Occ (R, E) = Occ (A, E)
        elsif V = E then Occ (R, E) = Occ (A, E) + 1
        elsif A (I) = E then Occ (R, E) = Occ (A, E) - 1
        else Occ (R, E) = Occ (A, E));

end Perm.Lemma_Subprograms;
