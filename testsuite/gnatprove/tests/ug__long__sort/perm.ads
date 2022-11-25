with SPARK.Big_Integers;   use SPARK.Big_Integers;
with Nat_Multisets;        use Nat_Multisets;
with Sort_Types;           use Sort_Types;

package Perm with SPARK_Mode, Ghost is
   use Nat_Multisets;

   function Occurrences (Values : Nat_Array; Lst : Integer) return Multiset is
     (if Lst < Values'First then Empty_Multiset
      else Add (Occurrences (Values, Lst - 1), Values (Lst)))
   with Subprogram_Variant => (Decreases => Lst),
     Pre => Lst <= Values'Last;

   function Occurrences (Values : Nat_Array) return Multiset is
     (Occurrences (Values, Values'Last));

   function Occ (Values : Nat_Array; N : Natural) return Big_Natural is
     (Nb_Occurence (Occurrences (Values), N));

   function Is_Perm (Left, Right : Nat_Array) return Boolean is
     (Occurrences (Left) = Occurrences (Right));

end Perm;
