package Perm with SPARK_Mode is
   subtype True_Bool is Boolean range True .. True;
   subtype Index is Integer range 1 .. 100;
   subtype Nb_Occ is Integer range 0 .. 100;
   type Nat_Array is array (Index range <>) of Natural;

   function Remove_Last (A : Nat_Array) return Nat_Array with
     Pre  => A'Length > 0,
     Post => Remove_Last'Result'First = A'First
     and then Remove_Last'Result'Last = A'Last - 1
     and then (for all I in Remove_Last'Result'Range =>
                 Remove_Last'Result (I) = A (I));

   function Occ_Def (A : Nat_Array; E : Natural) return Nb_Occ is
     (if A'Length = 0 then 0
      elsif A (A'Last) = E then Occ_Def (Remove_Last (A), E) + 1
      else Occ_Def (Remove_Last (A), E))
   with
     Post => Occ_Def'Result <= A'Length;

   function Occ (A : Nat_Array; E : Natural) return Nb_Occ is (Occ_Def (A, E))
   with
     Post => Occ'Result <= A'Length;

   function Occ_Eq (A, B : Nat_Array; E : Natural) return True_Bool with
     Pre  => A = B,
     Post => (if Occ_Eq'Result then Occ (A, E) = Occ (B, E));

   function Set (A : Nat_Array; I : Index; V : Natural) return Nat_Array with
     Pre  => I in A'Range,
     Post => Set'Result'First = A'First and then Set'Result'Last = A'Last
     and then Set'Result (I) = V
     and then (for all J in A'Range =>
                 (if I /= J then Set'Result (J) = A (J)));

   function Occ_Set (A : Nat_Array; I : Index; V, E : Natural) return True_Bool with
     Pre  => I in A'Range,
     Post =>
       (if Occ_Set'Result then
          (if V = A (I) then Occ (Set (A, I, V), E) = Occ (A, E)
               elsif V = E then Occ (Set (A, I, V), E) = Occ (A, E) + 1
               elsif A (I) = E then Occ (Set (A, I, V), E) = Occ (A, E) - 1
               else Occ (Set (A, I, V), E) = Occ (A, E)));

   function Is_Perm (A, B : Nat_Array) return Boolean is
     (for all E in Natural => Occ (A, E) = Occ (B, E));

end Perm;
