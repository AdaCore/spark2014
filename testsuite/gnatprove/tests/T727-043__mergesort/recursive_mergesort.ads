with Ada.Containers; use Ada.Containers;
with Ada.Containers.Functional_Maps;

package Recursive_Mergesort with SPARK_Mode is

   subtype Index is Positive range 1 .. Positive'Last - 1;

   type Arr is array (Index range <>) of Integer;

   package Multi_Sets with Ghost is

      package Occ_Map is new Ada.Containers.Functional_Maps
        (Key_Type     => Integer,
         Element_Type => Positive);
      type Multi_Set is new Occ_Map.Map;
      --  A multiset is a map from elements to their number of occurrences. This
      --  number is positive, as no occurrence means that the element is not in
      --  the map.

      function Is_Add (Occ : Multi_Set; K :Integer; Res : Multi_Set) return Boolean is
        (if Has_Key (Occ, K) then
              Same_Keys (Res, Occ)
         and then Get (Res, K) - 1 = Get (Occ, K)
         and then Elements_Equal_Except (Res, Occ, K)
         else Has_Key (Res, K)
         and then Get (Res, K) = 1
         and then Occ <= Res
         and then Keys_Included_Except (Res, Occ, K));
      --  Return True if Res is the result of adding an occurrence for K in Occ

      function Is_Merge (Left, Right, Result : Multi_Set) return Boolean is
        (Keys_Included (Left, Result)
         and then Keys_Included (Right, Result)
         and then (for all K of Result =>
                       (if Has_Key (Left, K) and Has_Key (Right, K) then
                               Get (Result, K) - Get (Right, K) = Get (Left, K)
                        elsif Has_Key (Left, K) then
                               Get (Result, K) = Get (Left, K)
                        else Has_Key (Right, K) and then
                        Get (Result, K) = Get (Right, K))));
      --  Return True if Result is the merge of Left and Right

      ------------
      -- Lemmas --
      ------------

      --  These lemmas are all proved automatically in an empty context, but
      --  they are useful to get their result when the context overwhelms the
      --  prover.

      procedure Prove_Add_Merge_L (Left1, Left2, Right, Res1, Res2 : Multi_Set; K : Integer) with
        Pre => Is_Add (Left1, K, Left2) and Is_Add (Res1, K, Res2) and Is_Merge (Left1, Right, Res1),
        Post => Is_Merge (Left2, Right, Res2);

      procedure Prove_Add_Merge_R (Left, Right1, Right2, Res1, Res2 : Multi_Set; K : Integer) with
        Pre => Is_Add (Right1, K, Right2) and Is_Add (Res1, K, Res2) and Is_Merge (Left, Right1, Res1),
        Post => Is_Merge (Left, Right2, Res2);

      procedure Prove_Add_Eq (Occ1, Occ2, Res1, Res2 : Multi_Set; K : Integer) with
        Pre  => Occ1 = Occ2 and Is_Add (Occ1, K, Res1) and Is_Add (Occ2, K, Res2),
        Post => Res1 = Res2;

      procedure Prove_Merge_Eq (Left1, Left2, Right1, Right2, Res1, Res2 : Multi_Set) with
        Pre  => Left1 = Left2 and Right1 = Right2 and Is_Merge (Left1, Right1, Res1) and Is_Merge (Left2, Right2, Res2),
        Post => Res1 = Res2;
   end Multi_Sets;
   use Multi_Sets;

   function Occurrences (A : Arr; I : Positive; J : Natural) return Multi_Set with
     Ghost,
     Pre => J < I or else (I in A'Range and J in A'Range),
     Post => J < I or else
     (Length (Occurrences'Result) <= Count_Type (J - I + 1)
      and (for all K of Occurrences'Result => Get (Occurrences'Result, K) <= J - I + 1)),
     Contract_Cases =>
       (J < I  => Is_Empty (Occurrences'Result) and Length (Occurrences'Result) = 0,
        others => Is_Add (Occurrences (A, I, J - 1), A (J), Occurrences'Result)),
     Subprogram_Variant => (Decreases => J),
     Annotate => (GNATprove, Terminating);
   --  Construct a multiset containing the occurrences of each element in an array

   function Is_Sorted (A : Arr) return Boolean is
     (for all I in A'Range =>
        (for all J in A'Range =>
             (if I <= J then A(I) <= A(J))))
   with Ghost;
   --  The array is sorted in ascending order

   procedure Merge(A : in out Arr; L, M, R : in Positive) with
     Pre => (L in A'Range and R in A'Range)
       and then L <= R
       and then M in L..R
       and then Is_Sorted (A (L .. M))
       and then Is_Sorted (A (M + 1 .. R)),
     Post => Occurrences (A, L, R) = Occurrences (A'Old, L, R)
     and Is_Sorted (A (L .. R))
     and A (A'First .. L - 1) = A'Old (A'First .. L - 1)
     and A (R + 1 .. A'Last) = A'Old (R + 1 .. A'Last);

   procedure Recursive_Mergesort(A : in out Arr; L, R: Positive) with
     Pre => A'Length >= 1
     and then (L in A'Range and R in A'Range)
     and then L <= R,
     Post => Occurrences (A, L, R) = Occurrences (A'Old, L, R)
     and Is_Sorted (A (L .. R))
     and A (A'First .. L - 1) = A'Old (A'First .. L - 1)
     and A (R + 1 .. A'Last) = A'Old (R + 1 .. A'Last),
     Subprogram_Variant => (Increases => L, Decreases => R);

end Recursive_Mergesort;
