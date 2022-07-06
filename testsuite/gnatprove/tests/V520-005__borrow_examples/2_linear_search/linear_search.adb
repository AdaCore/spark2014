package body Linear_Search with SPARK_Mode is

   function Linear_Search (L : access constant List_Cell; V : Integer) return Big_Natural is
      X : access constant List_Cell := L;
      I : Big_Positive := 1;
   begin
      while X /= null loop

         --  Variant to ensure termination of Linear_Search

         pragma Loop_Variant (Structural => X);

         --  I - 1 elements have been traversed already

         pragma Loop_Invariant (I = Length (X)'Loop_Entry - Length (X) + 1);

         --  V has not been found during the traversal

         pragma Loop_Invariant (for all K in Interval'(1, I - 1) => Nth (L, K) /= V);

         --  The sublist starting at I in L is X.
         --  Note that we need not use a pledge here, as X cannot be used to
         --  modify L.

         pragma Loop_Invariant
           (for all K in Interval'(I, Length (L)) => Nth (L, K) = Nth (X, K - I + 1));

         if X.Data.all = V then
            pragma Assert (Nth (L, I) = V);
            return I;
         end if;

         X := X.Next;
         I := I + 1;
      end loop;
      return 0;
   end Linear_Search;

   function Linear_Search (L : access List_Cell; V : Integer) return access Integer is
      I : Big_Natural := 0 with Ghost;
      --  Number of elements that have already been traversed

      X : access List_Cell := L;
   begin
      while X /= null loop
         pragma Loop_Variant (Structural => X);

         --  I elements have been traversed already

         pragma Loop_Invariant (I = Length (X)'Loop_Entry - Length (X));

         --  V has not been found during the traversal

         pragma Loop_Invariant (for all K in Interval'(1, I) => Nth (L, K) /= V);

         --  The sublist starting at I in L is X

         pragma Loop_Invariant
           (for all K in Interval'(I + 1, Length (L)) => Nth (X, K - I) = Nth (L, K));

         --  Pledge: the first I elements of L are frozen

         pragma Loop_Invariant
           (Length (At_End (L)) = Length (At_End (X)) + I);
         pragma Loop_Invariant
           (for all K in Interval'(1, I) => Nth (At_End (L), K) = Nth (L, K));

         --  Pledge: the rest are designated by X

         pragma Loop_Invariant
           (for all K in Interval'(I + 1, Length (At_End (L))) => Nth (At_End (L), K) = Nth (At_End (X), K - I));

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
