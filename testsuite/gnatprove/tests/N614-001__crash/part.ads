package Part
with SPARK_Mode
is

   type Set is array (Positive range <>) of Integer;

   function Mem (X : Set; Elt : Integer) return Boolean is
     (for some I in X'Range => Elt = X (I));

   function Subset (X, Y : Set) return Boolean is
     (for all I in X'Range => Mem (Y, X (I)));

   function Same_Set (X, Y : Set) return Boolean is
     (Subset (X, Y) and then Subset (Y, X));

   function Disjoint (X, Y : Set) return Boolean is
      (for all I in X'Range => not Mem (Y, X (I)));

   type Partition is array (Positive range <>) of Positive;

   function Ascending (P : Partition) return Boolean is
     (P'Length < 2 or else
        (for all I in P'First .. P'Last - 1 => P (I) < P (I + 1)));

   function Is_Partition (S : Set; P : Partition) return Boolean
     is
     (P'Length < S'Length
      and then Ascending (P)
      and then (for all I in P'Range => P (I) in S'Range));

   function Disjoint_Or_Subset (A, B : Set) return Boolean is
     (Disjoint (A, B) or else Subset (A, B));

   function Get_Part (A : Set; P : Partition; I : Positive) return Set
     with Pre => Is_Partition (A, P) and then I in P'Range;

   function Get_Part (A : Set; P : Partition; I : Positive) return Set is
     (if I = P'First then A (A'First .. P (I) - 1)
      else A (P (I - 1) .. P (I) - 1));

   procedure Refine
     (A        : in out Set;
      P        : Partition;
      X        : Set;
      NP       : out Partition;
      Num_Part : out Natural)
     with Pre =>
       Subset (X, A) and then Is_Partition (A, P)
       and then A'Length - 1 = NP'Length,
     Post =>
       Is_Partition (A, NP (NP'First .. NP'First + Num_Part - 1))
       and then Same_Set (A'Old, A)
       and then
         (for all I in NP'First .. NP'First + Num_Part - 1 =>
            Disjoint_Or_Subset
              (Get_Part (A, NP (NP'First .. NP'First + Num_Part - 1), I), X));

end Part;
