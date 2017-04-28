package body Pair_Insertion_Sort with
  SPARK_Mode
is
   procedure Swap (Values : in out Arr;
                   X      : in     Index;
                   Y      : in     Index)
   with
     Pre  => X in Values'Range
       and then Y in Values'Range
       and then X /= Y,
     Post => Is_Perm (Values'Old, Values)
       and then Values (X) = Values'Old (Y)
       and then Values (Y) = Values'Old (X)
       and then (for all Z in Values'Range =>
                   (if Z /= X and Z /= Y then Values (Z) = Values'Old (Z)))
   is
      Temp : Integer;

      --  Ghost variables
      Init   : constant Arr (Values'Range) := Values with Ghost;
      Interm : Arr (Values'Range) with Ghost;

      procedure Prove_Perm With
        Ghost,
        Global => (Interm, Init, Y, X, Values),
        Pre  => X in Values'Range
          and then Y in Values'Range
          and then Is_Set (Init, X, Init (Y), Interm)
          and then Is_Set (Interm, Y, Init (X), Values),
        Post => Is_Perm (Init, Values)
      is
      begin
         for E in Integer loop
            Occ_Set (Init, X, Init (Y), E, Interm);
            Occ_Set (Interm, Y, Init (X), E, Values);
            pragma Loop_Invariant
              (for all F in Integer'First .. E =>
                 Occ (Values, F) = Occ (Init, F));
         end loop;
      end Prove_Perm;

   begin
      Temp       := Values (X);
      Values (X) := Values (Y);

      --  Ghost code
      pragma Assert (Is_Set (Init, X, Init (Y), Values));
      Interm := Values;

      Values (Y) := Temp;

      --  Ghost code
      pragma Assert (Is_Set (Interm, Y, Init (X), Values));
      Prove_Perm;
   end Swap;

   procedure Sort (A : in out Arr) is
      I, J, X, Y, Z : Integer;
      B : constant Arr(A'Range) := A with Ghost;
   begin
      I := 0;
      while I < A'Length-1 loop
         X := A(I);
         Y := A(I+1);
         if X < Y then
            Z := X;
            X := Y;
            Y := Z;
         end if;

         J := I - 1;
         while J >= 0 and then A(J) > X loop
            Swap (A, J+2, J);
            --  loop invariant for absence of run-time errors
            pragma Loop_Invariant (J in 0 .. A'Length-3);
            --  loop invariant for sorting
            pragma Loop_Invariant (Sorted (A, 0, J-1));
            pragma Loop_Invariant (Sorted (A, J+2, I+1));
            pragma Loop_Invariant (if J > 0 then A(J+2) >= A(J-1));
            pragma Loop_Invariant (A(J+2) > X);
            --  loop invariant for permutation
            pragma Loop_Invariant (Is_Perm (B, A));
            pragma Loop_Invariant ((A(J) = X and A(J+1) = Y) or (A(J) = Y and A(J+1) = X));
            J := J - 1;
         end loop;
         if A(J+2) /= X then
            Swap (A, J+2, J+1);
         end if;

         while J >= 0 and then A(J) > Y loop
            Swap (A, J+1, J);
            --  loop invariant for absence of run-time errors
            pragma Loop_Invariant (J in 0 .. A'Length-3);
            --  loop invariant for sorting
            pragma Loop_Invariant (Sorted (A, 0, J-1));
            pragma Loop_Invariant (Sorted (A, J+1, I+1));
            pragma Loop_Invariant (if J > 0 then A(J+1) >= A(J-1));
            pragma Loop_Invariant (A(J+1) > Y);
            --  loop invariant for permutation
            pragma Loop_Invariant (Is_Perm (B, A));
            pragma Loop_Invariant (A(J) = Y);
            J := J - 1;
         end loop;

         --  loop invariant for absence of run-time errors
         pragma Loop_Invariant (I in 0 .. A'Length-2);
         --  loop invariant for sorting
         pragma Loop_Invariant (J in -1 .. A'Length-3);
         pragma Loop_Invariant (Sorted (A, 0, I+1));
         --  loop invariant for permutation
         pragma Loop_Invariant (Is_Perm (B, A));
         I := I+2;
      end loop;

      if I = A'Length-1 then
         Y := A(I);
         J := I - 1;
         while J >= 0 and then A(J) > Y loop
            Swap (A, J+1, J);
            --  loop invariant for absence of run-time errors
            pragma Loop_Invariant (J in 0 .. A'Length-2);
            --  loop invariant for sorting
            pragma Loop_Invariant (Sorted (A, 0, J-1));
            pragma Loop_Invariant (Sorted (A, J+1, A'Length-1));
            pragma Loop_Invariant (if J > 0 then A(J+1) >= A(J-1));
            pragma Loop_Invariant (A(J+1) > Y);
            --  loop invariant for permutation
            pragma Loop_Invariant (Is_Perm (B, A));
            pragma Loop_Invariant (A(J) = Y);
            J := J - 1;
         end loop;
      end if;
   end Sort;

end Pair_Insertion_Sort;
