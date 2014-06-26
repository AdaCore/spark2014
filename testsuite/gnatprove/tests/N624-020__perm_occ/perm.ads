package Perm with SPARK_Mode is
   subtype Index is Integer range 1 .. 100;
   subtype Nb_Occ is Integer range 0 .. 100;
   type Nat_Array is array (Index range <>) of Natural;

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

   function Is_Perm (A, B : Nat_Array) return Boolean is
     (for all E in Natural => Occ (A, E) = Occ (B, E));

end Perm;
