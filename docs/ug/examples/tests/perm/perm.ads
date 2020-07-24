with Sort_Types; use Sort_Types;

package Perm with SPARK_Mode, Ghost is
   subtype Nb_Occ is Integer range 0 .. 100;

   function Remove_Last (A : Nat_Array) return Nat_Array is
     (A (A'First .. A'Last - 1))
   with Pre  => A'Length > 0;

   function Occ_Def (A : Nat_Array; E : Natural) return Nb_Occ is
     (if A'Length = 0 then 0
      elsif A (A'Last) = E then Occ_Def (Remove_Last (A), E) + 1
      else Occ_Def (Remove_Last (A), E))
   with
     Post => Occ_Def'Result <= A'Length,
     Subprogram_Variant => (Decreases => A'Length);
   pragma Annotate (GNATprove, Terminating, Occ_Def);

   function Occ (A : Nat_Array; E : Natural) return Nb_Occ is (Occ_Def (A, E))
   with
     Post => Occ'Result <= A'Length;

   function Is_Perm (A, B : Nat_Array) return Boolean is
     (for all E in Natural => Occ (A, E) = Occ (B, E));

end Perm;
