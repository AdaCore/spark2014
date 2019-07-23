package body GHC_Sort with SPARK_Mode is
   function Cut (S : Int_Array) return Cut_Points is
      Cut : Cut_Points (1 .. S'Length + 1) := (others => 1);
      Top : Positive := 1;
      X   : Positive := S'First;
      Y   : Positive := S'First + 1;
      Inc : Boolean;
   begin

      while Y in S'Range loop -- n is the length of sequence s
         pragma Loop_Invariant (X in S'Range);
         pragma Loop_Invariant (X = Y - 1);
         pragma Loop_Invariant (Top in 1 .. X);
         pragma Loop_Invariant (Cut (1) = 1);
         pragma Loop_Invariant (X = Cut (Top));
         pragma Loop_Invariant
           (for all K in 1 .. Top => Cut (K) in 1 .. X);
         pragma Loop_Invariant
           (for all K in 1 .. Top - 1 => Cut (K + 1) > Cut (K));
         pragma Loop_Invariant
           (for all K in 1 .. Top - 1 =>
              ((for all L in Cut (K) + 1 .. Cut (K + 1) - 1 => S (L - 1) < S (L))
               and then S (Cut (K + 1)) <= S (Cut (K + 1) - 1))
            or else
              ((for all L in Cut (K) + 1 .. Cut (K + 1) - 1 => S (L - 1) >= S (L))
               and then S (Cut (K + 1)) > S (Cut (K + 1) - 1)));

         Inc := S (X) < S (Y); -- currently in increasing segment?
         while Y in S'Range and then (S (Y - 1) < S (Y)) = Inc loop
            pragma Loop_Invariant (Y'Loop_Entry <= Y);
            pragma Loop_Invariant
              (for all K in Y'Loop_Entry .. Y => (S (K - 1) < S (K)) = Inc);
            Y := Y + 1;
         end loop;
         Top := Top + 1;
         Cut (Top) := Y; -- extend cut by adding y to its end
         X := Y;
         Y := X + 1;
      end loop;

      if X <= S'Last then
         Top := Top + 1;
         Cut (Top) := S'Length + 1;
      end if;

      return Cut (1 .. Top);
   end Cut;

   function Merge (S1, S2 : Int_Array) return Int_Array is
      J1, J2, J : Positive := 1;
   begin
      return R : Int_Array (1 .. S1'Length + S2'Length) do
         R := (others => 0);
         while J1 in S1'Range and then J2 in S2'Range loop
            pragma Loop_Invariant (J = J1 + J2 - 1);
            pragma Loop_Invariant (if J > 1 then R (J - 1) <= S1 (J1));
            pragma Loop_Invariant (if J > 1 then R (J - 1) <= S2 (J2));
            pragma Loop_Invariant
              (for all L in 2 .. J - 1 => R (L - 1) <= R (L));
            if S1 (J1) < S2 (J2) then
               R (J) := S1 (J1);
               J1 := J1 + 1;
            else
               R (J) := S2 (J2);
               J2 := J2 + 1;
            end if;
            J := J + 1;
         end loop;
         -- append any remaining tail of S1 or S2
         while J1 in S1'Range loop
            pragma Loop_Invariant (J = J1 + J2 - 1);
            pragma Loop_Invariant
              (for all L in 2 .. J - 1 => R (L - 1) <= R (L));
            pragma Loop_Invariant (if J > 1 then R (J - 1) <= S1 (J1));
            R (J) := S1 (J1);
            J := J + 1;
            J1 := J1 + 1;
         end loop;
         while J2 in S2'Range loop
            pragma Loop_Invariant (J = J1 + J2 - 1);
            pragma Loop_Invariant
              (for all L in 2 .. J - 1 => R (L - 1) <= R (L));
            pragma Loop_Invariant (if J > 1 then R (J - 1) <= S2 (J2));
            R (J) := S2 (J2);
            J := J + 1;
            J2 := J2 + 1;
         end loop;
      end return;
   end Merge;

   function S_Reverse (S : Int_Array) return Int_Array is
      R : Int_Array (S'Range);
      J : Natural := 0;
   begin
      R := (others => 0);
      for I in reverse S'Range loop
         pragma Loop_Invariant (J = S'Length - I);
         pragma Loop_Invariant
           (for all K in I + 1 .. S'Last => R (K) = S (S'Length - K + 1));
         J := J + 1;
         R (I) := S (J);
      end loop;
      return R;
   end S_Reverse;

   --  Type for a list of sequences

   type Int_Array_List_Cell (L : Natural);
   type Int_Array_List is access Int_Array_List_Cell;
   type Int_Array_List_Cell (L : Natural) is record
      Value : Int_Array (1 .. L);
      Next  : Int_Array_List;
   end record;

   --  Recursive predicate: All elements of a list are sorted

   function All_Sorted (L : Int_Array_List) return Boolean is
     (if L = null then True
      else (for all K in 2 .. L.L => L.Value (K - 1) <= L.Value (K))
      and then All_Sorted (L.Next));
   pragma Annotate (GNATprove, Terminating, All_Sorted);

   --  Length of the concatenation of all subsequences in the list, saturated
   --  at Integer'Last if necessary.

   function Sum_Length_Aux (L : Int_Array_List) return Natural is
     (if L = null then 0
      elsif L.L <= Integer'Last - Sum_Length_Aux (L.Next) then
           L.L + Sum_Length_Aux (L.Next)
      else Integer'Last);
   pragma Annotate (GNATprove, Terminating, Sum_Length_Aux);

   function Sum_Length (L : Int_Array_List) return Natural is
     (Sum_Length_Aux (L));

   --  Go over the list in a recursive way, merging elements by two along the
   --  way.

   procedure Merge_By_Two (L : in out Int_Array_List) with
     Pre  => Sum_Length (L) < Integer'Last and then All_Sorted (L),
     Post => Sum_Length (L) = Sum_Length (L)'Old
     and then All_Sorted (L);

   procedure Merge_By_Two (L : in out Int_Array_List) is
   begin
      if L = null or else L.Next = null then
         return;
      else
         L := new Int_Array_List_Cell'
           (L.L + L.Next.L, Merge (L.Value, L.Next.Value), L.Next.Next);
         Merge_By_Two (L.Next);
      end if;
   end Merge_By_Two;

   function Sort (S : Int_Array) return Int_Array is

      --  Compute the cut sequence

      Cuts : Cut_Points := Cut (S);
      L    : Int_Array_List;
   begin

      --  Cut the sequence in subsequences at cut points, reversing
      --  subsequences if needed.

      for C in 1 .. Cuts'Last - 1 loop
         pragma Loop_Invariant (All_Sorted (L));
         pragma Loop_Invariant (Sum_Length (L) = Cuts (C) - 1);
         declare
            SS : Int_Array := S (Cuts (C) .. Cuts (C + 1) - 1);
         begin
            if SS'Length > 1 and then SS (2) <= SS (1) then
               SS := S_Reverse (SS);
            end if;
            L := new Int_Array_List_Cell' (SS'Length, SS, L);
         end;
      end loop;

      -- Merge them pairwise until there is at most one left

      while L /= null and then L.Next /= Null loop
         pragma Loop_Invariant (All_Sorted (L));
         pragma Loop_Invariant (Sum_Length (L) = S'Length);
         Merge_By_Two (L);
      end loop;
      return (if L = null then S else L.Value);
   end Sort;

end GHC_Sort;
