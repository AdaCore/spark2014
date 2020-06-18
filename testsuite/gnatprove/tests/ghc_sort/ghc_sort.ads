package GHC_Sort with SPARK_Mode is
   type Int_Array is array (Positive range <>) of Integer with
     Predicate => Int_Array'First = 1;
   type Cut_Points is array (Positive range <>) of Positive;

   function Cut (S : Int_Array) return Cut_Points with
     Pre  => S'Last < Integer'Last - 1,
     Post => Cut'Result'First = 1 and then Cut'Result'Last in 1 .. S'Length + 1

     --  We return a sequence of cuts

     and then (for all C of Cut'Result => C in 1 .. S'Length + 1)

     --  Ranging over the whole sequence

     and then Cut'Result (1) = 1
     and then Cut'Result (Cut'Result'Last) = S'Length + 1

     --  There are no empty subsequences

     and then
       (for all K in 1 .. Cut'Result'Last - 1 => Cut'Result (K + 1) > Cut'Result (K))

     --  Subsequences are ordered and maximal (to the right)

     and then
       (for all K in 1 .. Cut'Result'Last - 1 =>
          ((for all L in Cut'Result (K) + 1 .. Cut'Result (K + 1) - 1 => S (L - 1) < S (L))
           and then (Cut'Result (K + 1) = S'Length + 1
                     or else S (Cut'Result (K + 1)) <= S (Cut'Result (K + 1) - 1)))
        or else
          ((for all L in Cut'Result (K) + 1 .. Cut'Result (K + 1) - 1 => S (L - 1) >= S (L))
           and then (Cut'Result (K + 1) = S'Length + 1
                     or else S (Cut'Result (K + 1)) > S (Cut'Result (K + 1) - 1))));

   function Merge (S1, S2 : Int_Array) return Int_Array with
     Pre  => S1'Length < Integer'Last - S2'Length
     and then (for all L in 2 .. S1'Last => S1 (L - 1) <= S1 (L))
     and then (for all L in 2 .. S2'Last => S2 (L - 1) <= S2 (L)),
     Post => Merge'Result'Length = S1'Length + S2'Length
     and then (for all L in 2 .. Merge'Result'Last => Merge'Result (L - 1) <= Merge'Result (L));
   --  Merge two sorted sequences preserving order.
   --  Merge is specified only partially, we are missing the fact that the
   --  result of Merge is a permutation of S1 & S2.

   function S_Reverse (S : Int_Array) return Int_Array with
     Pre  => S'Length < Integer'Last,
     Post => S_Reverse'Result'Length = S'Length
     and then (for all L in S'Range => S_Reverse'Result (L) = S (S'Length - L + 1));
   --  Reverse a sequence

   procedure Sort (S : Int_Array; Result : out Int_Array) with
     Pre  => S'Length < Integer'Last - 1 and Result'First = 1 and Result'Last = S'Last,
     Post => (for all L in 2 .. Result'Last => Result (L - 1) <= Result (L));
   --  Sort a sequence using GHC sort. Sort it specified only partially, we are
   --  missing the fact that the result of Sort is a permuation of S.

end GHC_Sort;
