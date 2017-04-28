with Types; use Types;

package Perm with
  SPARK_Mode,
  Ghost
is
   subtype Nb_Occ is Natural;

   function Remove_Last (A : Arr) return Arr is
     (A (A'First .. A'Last - 1))
   with Pre => A'Length > 0;

   function Occ_Def (A : Arr; E : Integer) return Nb_Occ is
     (if A'Length = 0 then 0
      elsif A (A'Last) = E then Occ_Def (Remove_Last (A), E) + 1
      else Occ_Def (Remove_Last (A), E))
   with Post => Occ_Def'Result <= A'Length;
   pragma Annotate (GNATprove, Terminating, Occ_Def);
   pragma Annotate (GNATprove, False_Positive, "terminate",
                    "Occ_Def is called recursively on a strictly smaller array");

   function Occ (A : Arr; E : Integer) return Nb_Occ is (Occ_Def (A, E))
   with
     Post => Occ'Result <= A'Length;

   function Is_Set (A : Arr; I : Index; V : Integer; R : Arr) return Boolean
   is (R'First = A'First
       and then R'Last = A'Last
       and then R (I) = V
       and then (for all J in A'Range => (if I /= J then R (J) = A (J))))
   with
     Pre => I in A'Range;

   procedure Occ_Set (A : Arr; I : Index; V, E : Integer; R : Arr)
   with
     Global => null,
     Pre    => I in A'Range
       and then Is_Set (A, I, V, R),
     Post   =>
       (if V = A (I) then Occ (R, E) = Occ (A, E)
        elsif V = E then Occ (R, E) = Occ (A, E) + 1
        elsif A (I) = E then Occ (R, E) = Occ (A, E) - 1
        else Occ (R, E) = Occ (A, E));

   function Is_Perm (A, B : Arr) return Boolean is
     (for all E in Integer => Occ (A, E) = Occ (B, E));

end Perm;
