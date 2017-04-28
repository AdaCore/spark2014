with Types; use Types;
with Perm;  use Perm;

package Pair_Insertion_Sort with
  SPARK_Mode
is
   function Sorted (A : Arr; I, J : Integer) return Boolean is
      (for all K in I .. J-1 => A(K) <= A(K+1))
   with Ghost,
        Pre => J > Integer'First
          and then (if I <= J then I in A'Range and J in A'Range);

   procedure Sort (A : in out Arr) with
     Post => Sorted (A, 0, A'Length-1)
       and then Is_Perm (A'Old, A);

end Pair_Insertion_Sort;
