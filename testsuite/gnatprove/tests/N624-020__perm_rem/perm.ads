package Perm with SPARK_Mode is
   subtype True_Bool is Boolean range True .. True;
   subtype Index is Integer range 1 .. 100;
   type Nat_Array is array (Index range <>) of Natural;

   function Invariant (A : Nat_Array) return Boolean is
      (A'First = 1 and A'Last > 0);

   function Remove (A : Nat_Array; I : Index) return Nat_Array with
     Pre  => Invariant (A) and then I in A'Range,
     Post => Invariant (Remove'Result) and then
     Remove'Result'Last = A'Last - 1 and then
     (for all K in 1 .. I - 1 => A (K) = Remove'Result (K)) and then
     (for all K in I + 1 .. A'Last => A (K) = Remove'Result (K - 1)) and then
     (for all K in I .. A'Last - 1 => A (K + 1) = Remove'Result (K));

   function Remove_Swap (A : Nat_Array; I1, I2 : Index) return True_Bool with
     Pre  => Invariant (A) and then I1 in A'Range and then I2 in A'Range
     and then I1 < I2,
     Post => (if Remove_Swap'Result then
                Remove (Remove (A, I1), I2 - 1) =
                  Remove (Remove (A, I2), I1));

   function Remove_Eq (A, B : Nat_Array; I : Index) return True_Bool with
     Pre  => Invariant (A) and then Invariant (B) and then I in A'Range
     and then A = B,
     Post => (if Remove_Eq'Result then Remove (A, I) = Remove (B, I));

   function Is_Perm (A, B : Nat_Array) return Boolean with
     Pre => Invariant (A) and Invariant (B);

   function Is_Perm (A, B : Nat_Array) return Boolean is
     ((A'Length = 0 and then B'Length = 0)
      or else (for some Ia in A'Range =>
                   (for some Ib in B'Range => A (Ia) = B (Ib) and then
                    Is_Perm (Remove (A, Ia), Remove (B, Ib)))));
   pragma Annotate (GNATprove, Terminating, Is_Perm);
   function Perm_Reflexive (A, B : Nat_Array) return True_Bool with
     Pre  => Invariant (A) and then Invariant (B) and then A = B,
     Post => (if Perm_Reflexive'Result then Is_Perm (A, B));

   function Perm_Symmetric (A, B : Nat_Array) return True_Bool with
     Pre  => Invariant (A) and then Invariant (B) and then Is_Perm (A, B),
     Post => (if Perm_Symmetric'Result then Is_Perm (B, A));

   function Perm_Transitive (A, B, C : Nat_Array) return True_Bool with
     Pre  => Invariant (A) and then Invariant (B) and then Invariant (C) and then
     Is_Perm (A, B) and then Is_Perm (B, C),
     Post => (if Perm_Transitive'Result then Is_Perm (A, C));

   function Perm_Eq (A, B : Nat_Array) return True_Bool with
     Pre => Invariant (A) and then Invariant (B) and then Is_Perm (A, B),
     Post => (if Perm_Eq'Result then
                (for all Ia in A'Range =>
                     (for some Ib in B'Range => A (Ia) = B (Ib))));

   function Remove_Perm (A, B : Nat_Array; Ia, Ib : Index) return True_Bool with
     Pre => Invariant (A) and then Invariant (B) and then
     Ia in A'Range and then Ib in B'Range and then Is_Perm (A, B)
     and then A (Ia) = B (Ib),
     Post => (if Remove_Perm'Result then
                Is_Perm (Remove (A, Ia), Remove (B, Ib)));

end Perm;
