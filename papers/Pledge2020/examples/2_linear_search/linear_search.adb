package body Linear_Search with SPARK_Mode is

   function Linear_Search (L : access constant List_Cell; V : Integer) return Natural is
      X : access constant List_Cell := L;
      I : Positive := 1;
   begin
      while X /= null loop

         --  Variant to ensure termination of Linear_Search

         pragma Loop_Variant (Decreases => Length (X));

         --  I - 1 elements have been traversed already

         pragma Loop_Invariant (I = Length (X)'Loop_Entry - Length (X) + 1);

         --  V has not been found during the traversal

         pragma Loop_Invariant (for all K in 1 .. I - 1 => Nth (L, K) /= V);

         --  The sublist starting at I in L is X.
         --  Note that we need not use a pledge here, as X cannot be used to
         --  modify L.

         pragma Loop_Invariant
           (for all K in I .. Length (L) => Nth (L, K) = Nth (X, K - I + 1));

         if X.Data.all = V then
            pragma Assert (Nth (L, I) = V);
            return I;
         end if;

         X := X.Next;
         I := I + 1;
      end loop;
      return 0;
   end Linear_Search;

   function All_Data (R : access constant List_Cell) return Int_Seq is
   begin
      return A : Int_Seq do
         for N in 1 .. Length (R) loop
            pragma Loop_Invariant (Last (A) = N - 1);
            pragma Loop_Invariant
              (for all I in 1 .. N - 1 => Get (A, I) = Nth (R, I));
            A := Add (A, Nth (R, N));
         end loop;
      end return;
   end All_Data;

   function Linear_Search (L : access List_Cell; V : Integer) return access Integer is
      Old_L : constant Int_Seq := All_Data (L) with Ghost;
      --  Values of L at the beginning of the loop

      I     : Natural := 0 with Ghost;
      --  Number of elements that have already been traversed

      X : access List_Cell := L;
   begin
      while X /= null loop

         --  I elements have been traversed already

         pragma Loop_Invariant (I = Length (X)'Loop_Entry - Length (X));

         --  V has not been found during the traversal

         pragma Loop_Invariant (for all K in 1 .. I => Nth (L, K) /= V);

         --  The sublist starting at I in L is X

         pragma Loop_Invariant
           (for all K in I + 1 .. Length (L) => Nth (X, K - I) = Nth (L, K));

         --  Pledge: the first I elements of L are frozen

         pragma Loop_Invariant
           (Pledge (X, Length (L) = Integer'Min (Integer'Last - I, Length (X)) + I));
         pragma Loop_Invariant
           (Pledge (X, (for all K in 1 .. I => Nth (L, K) = Get (Old_L, K))));

         --  Pledge: the rest are designated by X

         pragma Loop_Invariant
           (Pledge (X, (for all K in I + 1 .. Length (L) => Nth (L, K) = Nth (X, K - I))));

         I := I + 1;

         if X.Data.all = V then

            --  Assert that we have found the value to help the proof

            pragma Assert (Nth (L, I) = V);
            pragma Assert (I = Linear_Search (L, V));

            return X.Data;
         end if;

         X := X.Next;
      end loop;
      return null;
   end Linear_Search;

end Linear_Search;
