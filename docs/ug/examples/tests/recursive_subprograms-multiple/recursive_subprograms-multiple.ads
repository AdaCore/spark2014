package Recursive_Subprograms.Multiple with SPARK_Mode is
   type Nat_Array is array (Positive range <>) of Natural;

   function Max (A : Nat_Array; F, L : Positive) return Positive is
     (if F = L then F
      elsif A (F) > A (L) then Max (A, F, L - 1)
      else Max (A, F + 1, L))
   with Pre  => L in A'Range and F in A'Range and F <= L,
        Post => Max'Result in F .. L
         and then (for all I in F .. L => A (I) <= A (Max'Result)),
        Subprogram_Variant => (Increases => F, Decreases => L);
end Recursive_Subprograms.Multiple;
