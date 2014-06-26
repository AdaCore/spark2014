package Perm with SPARK_Mode is
   pragma Annotate (GNATprove, External_Axiomatization);
   subtype Index is Integer range 1 .. 100;
   type Nat_Array is array (Index range <>) of Natural;

   function Is_Perm (A, B : Nat_Array) return Boolean;

private
   pragma SPARK_Mode (Off);

   subtype Nb_Occ is Integer range 0 .. 100;

   function Remove_Last (A : Nat_Array) return Nat_Array is
     (A (A'First .. A'Last - 1))
   with Pre  => A'Length > 0;

   function Occ_Def (A : Nat_Array; E : Natural) return Nb_Occ is
     (if A'Length = 0 then 0
      elsif A (A'Last) = E then Occ_Def (Remove_Last (A), E) + 1
      else Occ_Def (Remove_Last (A), E))
   with
     Post => Occ_Def'Result <= A'Length;

   function Occ (A : Nat_Array; E : Natural) return Nb_Occ is (Occ_Def (A, E))
   with
     Post => Occ'Result <= A'Length;

   function Is_Perm (A, B : Nat_Array) return Boolean is
     (for all E in Natural => Occ (A, E) = Occ (B, E));
end Perm;
