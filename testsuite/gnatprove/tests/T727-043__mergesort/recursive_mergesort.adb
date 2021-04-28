package body Recursive_Mergesort with SPARK_Mode is

   ------------------
   -- Local Lemmas --
   ------------------

   --  These lemmas are factored out and proved by induction

   procedure Prove_Cut (A : Arr; L, M, R : Positive) with
     Ghost,
     Pre => (L in A'Range and R in A'Range)
       and then L <= R
       and then M in L .. R,
     Post => Is_Merge (Occurrences (A, L, M),
                       Occurrences (A, M + 1, R),
                       Occurrences (A, L, R)),
     Subprogram_Variant => (Decreases => R);
   --  When a slice is cut in two, the number of occurrences in the slice is
   --  the merge of the occurrences of the parts.

   procedure Prove_Eq (A1, A2 : Arr; I1 : Positive; J1 : Natural; I2 : Positive; J2 : Natural) with
     Ghost,
     Pre => (J1 < I1 or else (I1 in A1'Range and J1 in A1'Range))
     and then (J2 < I2 or else (I2 in A2'Range and J2 in A2'Range))
     and then A1 (I1 .. J1) = A2 (I2 .. J2),
     Post => Occurrences (A1, I1, J1) = Occurrences (A2, I2, J2),
     Subprogram_Variant => (Decreases => J1);
   --  When two slices are equal, they have the same occurrences

   ------------
   -- Bodies --
   ------------

   package body Multi_Sets is

      procedure Prove_Add_Merge_L (Left1, Left2, Right, Res1, Res2 : Multi_Set; K : Integer) is null;
      procedure Prove_Add_Merge_R (Left, Right1, Right2, Res1, Res2 : Multi_Set; K : Integer) is null;
      procedure Prove_Merge_Eq (Left1, Left2, Right1, Right2, Res1, Res2 : Multi_Set) is null;
      procedure Prove_Add_Eq (Occ1, Occ2, Res1, Res2 : Multi_Set; K : Integer) is null;

   end Multi_Sets;

   function Occurrences (A : Arr; I : Positive; J : Natural) return Multi_Set is
      Res : Multi_Set;
   begin
      if I <= J then
         Res := Occurrences (A, I, J - 1);
         if Has_Key (Res, A (J)) then
            Res := Set (Res, A (J), Get (Res, A (J)) + 1);
         else
            Res := Add (Res, A (J), 1);
         end if;
      end if;
      return Res;
   end Occurrences;

   procedure Prove_Cut (A : Arr; L, M, R : Positive) is
   begin
      if M /= R then
         Prove_Cut (A, L, M, R - 1);
      end if;
   end Prove_Cut;

   procedure Prove_Eq (A1, A2 : Arr; I1 : Positive; J1 : Natural; I2 : Positive; J2 : Natural) is
   begin
      if I1 <= J1 then
         Prove_Eq (A1, A2, I1, J1 - 1, I2, J2 - 1);
         Prove_Add_Eq (Occurrences (A1, I1, J1 - 1), Occurrences (A2, I2, J2 - 1), Occurrences (A1, I1, J1), Occurrences (A2, I2, J2), A1 (J1));
      end if;
   end Prove_Eq;

   procedure Recursive_Mergesort(A: in out Arr; L, R: Positive) is
      M        : Positive;
      A_old    : constant Arr := A with Ghost;
      A_interm : Arr (A'Range) with Ghost;
   begin
      if (L < R) then
         M := L + (R - L)/2;
         Recursive_Mergesort(A, L, M);
         A_interm := A;
         Recursive_Mergesort(A, M + 1, R);

         --  Prove that A (L .. R) and A_old (L .. R) have the same occurrences

         begin
            --  A and A_interm coincide on L .. M so they have the same occurrences

            Prove_Eq (A, A_interm, L, M, L, M);

            --  A_interm and A_old coincide on M + 1 .. R so they have the same occurrences

            Prove_Eq (A_interm, A_old, M + 1, R, M + 1, R);

            --  Occurrences of A (L .. R) is the merge of occurrences on A (L .. M) and A (M + 1 .. R)

            Prove_Cut (A, L, M, R);

            --  Occurrences of A_old (L .. R) is the merge of occurrences on A_old (L .. M) and A_old (M + 1 .. R)

            Prove_Cut (A_old, L, M, R);

            --  Occurrences of A_old (L .. R) and A (L .. R) are the merge of equal occurrences, they are equal

            Prove_Merge_Eq (Occurrences (A, L, M), Occurrences (A_old, L, M), Occurrences (A, M + 1, R), Occurrences (A_old, M + 1, R),  Occurrences (A, L, R), Occurrences (A_old, L, R));

            --  Summarize the proved property and erase the context

            pragma Assert_And_Cut (Occurrences (A, L, R) = Occurrences (A_old, L, R));
         end;

         Merge (A, L, M, R);
      end if;
   end Recursive_Mergesort;

   procedure Merge(A : in out Arr; L : in Positive;
                   M : in Positive; R : in Positive) is
      lii, rii, aii : Natural := 0;
      n1            : constant Positive := M - L + 1;
      n2            : constant Natural := R - M;
      A_copy        : constant Arr := A;
      A_iterm       : Arr (A'Range) with Ghost;
   begin
      while lii < n1 or rii < n2 loop

         if rii = n2
           or else (lii < n1 and then A_copy (L + lii) <= A_copy (M + 1 + rii))
         then
            A_iterm := A;
            A (L + aii) := A_copy (L + lii);

            --  Prove that A (L .. L + aii) is the merge of A_copy (L .. L + lii) and A_copy (M .. M + rii)

            Prove_Eq (A, A_iterm, L, L + aii - 1, L, L + aii - 1);
            Prove_Add_Merge_L (Occurrences (A_copy, L, L + lii - 1), Occurrences (A_copy, L, L + lii), Occurrences (A_copy, M + 1, M + 1 + rii - 1), Occurrences (A, L, L + aii - 1), Occurrences (A, L, L + aii), A_copy (L + lii));

            lii := lii + 1;
         else
            A_iterm := A;
            A (L + aii) := A_copy (M + 1 + rii);

            --  Prove that A (L .. L + aii) is the merge of A_copy (L .. L + lii - 1) and A_copy (M .. M + 1 + rii)

            Prove_Eq (A, A_iterm, L, L + aii - 1, L, L + aii - 1);
            Prove_Add_Merge_R (Occurrences (A_copy, L, L + lii - 1), Occurrences (A_copy, M + 1, M + 1 + rii - 1), Occurrences (A_copy, M + 1, M + 1 + rii), Occurrences (A, L, L + aii - 1), Occurrences (A, L, L + aii), A_copy (M + 1 + rii));

            rii := rii + 1;
         end if;
         aii := aii + 1;

         pragma Loop_Invariant (Is_Merge (Occurrences (A_copy, L, L + lii - 1), Occurrences (A_copy, M + 1, M + rii), Occurrences (A, L, L + aii - 1)));

         pragma Loop_Invariant (A (A'First .. L - 1) = A_copy (A'First .. L - 1));
         pragma Loop_Invariant (A (R + 1 .. A'Last) = A_copy (R + 1 .. A'Last));

         pragma Loop_Invariant (Is_Sorted (A (L .. L + aii - 1)));
         pragma Loop_Invariant (if lii < n1 then A (L + aii - 1) <= A_copy (L + lii));
         pragma Loop_Invariant (if rii < n2 then A (L + aii - 1) <= A_copy (M + 1 + rii));

         pragma Loop_Invariant(aii = lii + rii);
         pragma Loop_Invariant(lii <= n1 and rii <= n2);
      end loop;
      pragma Assert (Is_Sorted (A (L .. R)));

      --  Prove that A (L .. M) and A_copy (L .. M) have the same occurrences

      pragma Assert (Is_Merge (Occurrences (A_copy, L, M), Occurrences (A_copy, M + 1, R), Occurrences (A, L, R)));
      Prove_Cut (A_copy, L, M, R);
      Prove_Merge_Eq (Occurrences (A_copy, L, M), Occurrences (A_copy, L, M), Occurrences (A_copy, M + 1, R), Occurrences (A_copy, M + 1, R), Occurrences (A, L, R), Occurrences (A_copy, L, R));
   end Merge;

end Recursive_Mergesort;
