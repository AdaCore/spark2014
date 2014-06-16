package body Partition_Refinement with
  SPARK_Mode
is
   pragma Unevaluated_Use_Of_Old (Allow);

   -----------------------
   -- Local subprograms --
   -----------------------

   procedure Swap
     (A    : in out Set;
      J, K : Index)
   with
     Post => A = A'Old'Update (J => A'Old(K), K => A'Old(J));

   procedure Refine_One
     (A      : in out Set;
      D      : in out Inverse_Set;
      P      : in out Partition;
      F      : in     Inverse_Partition;
      X_Elem : in Positive)
   with
      Pre  => Length (P) < Count_Type(Partition_Index'Last) and then
              Contains (D, X_Elem) and then
              F(Element (D, X_Elem)) in 0 .. Partition_Index'Base (Length (P)) - 1 and then
              (for all J in Index => Contains (D, A(J))) and then
              (for all C in D => A (Element (D, C)) = Key (D, C)),
      Post => (for all K in Index => A(K) =
                 (if K = Element (D, X_Elem)'Old then
                    A'Old(Element (P, F(Element (D, X_Elem))).First'Old + Element (P, F(Element (D, X_Elem))).Count'Old)
                  elsif K = Index'(Element (P, F(Element (D, X_Elem))).First + Element (P, F(Element (D, X_Elem))).Count)'Old then
                    A(Element (D, X_Elem))'Old
                  else
                    A'Old(K))) and then
                Capacity (P) = Capacity (P)'Old and then
                Length (P) = Length (P)'Old and then
                (for all J in 0 .. Partition_Index(Length (P)) - 1 => Element (P, J).First = Element (P'Old, J).First) and then
                (for all J in 0 .. Partition_Index(Length (P)) - 1 => Element (P, J).Last = Element (P'Old, J).Last) and then
                (for all J in 0 .. Partition_Index(Length (P)) - 1 =>
                   Element (P, J).Count = Element (P'Old, J).Count + (if J = F(Element (D'Old, X_Elem)) then 1 else 0)) and then
                (for all J in Index => Contains (D, A(J))) and then
                (for all C in D => A (Element (D, C)) = Key (D, C)) and then
                (for all C in D'Old => Has_Element (D, C));

   procedure Make_New_Partitions
     (P : in out Partition;
      F : in out Inverse_Partition)
   with
      Pre  => --  P is at most half full, to make space for the refinement
              2 * Length (P) <= Capacity (P) and then
              Length (P) <= Count_Type(Partition_Index'Last / 2) and then
              --  F maps indexes to their partition
              (for all J in Index => F(J) in 0 .. Partition_Index'Base (Length (P)) - 1) and then
              (for all J in Index => J in Element (P, F(J)).First .. Element (P, F(J)).Last) and then
              (for all J in 0 .. Partition_Index'Base (Length (P)) - 1 => (for all K in Element (P, J).First .. Element (P, J).Last => F(K) = J)),
      Post => --  F still maps indexes to their partition
              (for all J in Index => F(J) in 0 .. Partition_Index'Base (Length (P)) - 1) and then
              (for all J in Index => J in Element (P, F(J)).First .. Element (P, F(J)).Last) and then
              (for all J in 0 .. Partition_Index'Base (Length (P)) - 1 => (for all K in Element (P, J).First .. Element (P, J).Last => F(K) = J));

   ----------
   -- Swap --
   ----------

   procedure Swap
     (A    : in out Set;
      J, K : Index)
   is
      Tmp : constant Positive := A(J);
   begin
      A(J) := A(K);
      A(K) := Tmp;
   end Swap;

   ----------------
   -- Refine_One --
   ----------------

   procedure Refine_One
     (A      : in out Set;
      D      : in out Inverse_Set;
      P      : in out Partition;
      F      : in     Inverse_Partition;
      X_Elem : in Positive)
   is
      I : constant Index := Element (D, X_Elem);
      P_Elem : Interval := Element (P, F(I));

      --  Proving that the index with which to swap is within bounds requires axiomatizing the count of elements in
      --  each partition that are in X. This would be done with an axiomatized unit in SPARK, with the axiomatization
      --  provided in Why3. For now, assume that this holds so that the range check when assigning to J is proved.
      pragma Assume (P_Elem.First + P_Elem.Count in Index);
      J : constant Index := P_Elem.First + P_Elem.Count;

      A_Old : constant Set := A;
      A_Update : constant Set := A_Old'Update (I => A_Old(J), J => A_Old(I));

   begin
      Swap (A, I, J);
      pragma Assert (A = A_Update);

      pragma Assert (for all C in D => (if Key (D, C) /= A(I) and Key (D, C) /= A(J) then A (Element (D, C)) = Key (D, C)));

      --  Intermediate assertion needed to prove the postcondition
      pragma Assert (for all J in Index => Contains (D, A(J)));
      Replace (D, A(I), I);
      pragma Assert (A = A_Update);

      pragma Assert (for all C in D => (if Key (D, C) /= A(I) and Key (D, C) /= A(J) then A (Element (D, C)) = Key (D, C)));
      pragma Assert (for all C in D => (if Key (D, C) = A(I) then A (Element (D, C)) = Key (D, C)));
      Replace (D, A(J), J);
      pragma Assert (A = A_Update);

      pragma Assert (for all C in D => (if Key (D, C) /= A(I) and Key (D, C) /= A(J) then A (Element (D, C)) = Key (D, C)));
      pragma Assert (for all C in D => (if Key (D, C) = A(I) then A (Element (D, C)) = Key (D, C)));
      pragma Assert (for all C in D => (if Key (D, C) = A(J) then A (Element (D, C)) = Key (D, C)));
      pragma Assert (for all C in D => A (Element (D, C)) = Key (D, C));
      P_Elem.Count := P_Elem.Count + 1;

      --  Replace_Element does not modify the capacity of the vector, but SPARK GPL 2014 does not prove it.
      --  Use a local assumption to convey this information.
      declare
         Save_Capacity : constant Count_Type := Capacity (P);
      begin
         Replace_Element (P, F(I), P_Elem);
         pragma Assume (Capacity (P) = Save_Capacity);
      end;

      pragma Assert (A = A_Update);
      --  This assumption is equivalent to the assertion above, although SPARK GPL 2014 does not prove it.
      pragma Assume (for all K in Index => A(K) = (if K = I then A_Old(J) elsif K = J then A_Old(I) else A_Old(K)));
   end Refine_One;

   -------------------------
   -- Make_New_Partitions --
   -------------------------

   procedure Make_New_Partitions
     (P : in out Partition;
      F : in out Inverse_Partition)
   is
      P_Elem, P_Prime : Interval;
      P_Prime_Index : Partition_Index;

      pragma Warnings (Off, "statement has no effect", Reason => "ghost code");
      P_Save : Partition := P;
      pragma Warnings (On, "statement has no effect", Reason => "ghost code");

   begin
      for J in 0 .. Partition_Index'Base (Length (P)) - 1 loop

         pragma Warnings (Off, "statement has no effect", Reason => "ghost code");
         P_Save := P;
         pragma Warnings (On, "statement has no effect", Reason => "ghost code");

         P_Elem := Element (P, J);
         if P_Elem.Count in 1 .. P_Elem.Last - P_Elem.First then
            P_Prime := Interval'(First => P_Elem.First + P_Elem.Count,
                                 Last  => P_Elem.Last,
                                 Count => 0);
            P_Elem.Last := P_Elem.First + P_Elem.Count - 1;
            P_Elem.Count := 0;

            --  Replace_Element does not modify the capacity of the vector, but SPARK GPL 2014 does not prove it.
            --  Use a local assumption to convey this information.
            declare
               Save_Capacity : constant Count_Type := Capacity (P);
            begin
               Replace_Element (P, J, P_Elem);
               pragma Assume (Capacity (P) = Save_Capacity);
            end;

            declare
               Save_Length : constant Count_Type := Length (P);
            begin
               P_Prime_Index := Partition_Index (Length (P));
               Append (P, P_Prime);
               pragma Assert (Length (P) = Save_Length + 1);
               pragma Assert (P_Prime_Index = Partition_Index (Length (P)) - 1);
               --  Append has the effect of setting at index Length(P) the value P_Prime, and not modifying any existing element. Use assumptions as this is not proved by SPARK GPL 2014.
               pragma Assume (Element (P, P_Prime_Index) = P_Prime);
               pragma Assume (for all K in Partition_Index range 0 .. P_Prime_Index - 1 => (if K /= J then Element (P, K) = Element (P_Save, K)));
            end;

            declare
               F_Loop_Entry : constant Inverse_Partition := F;
            begin
               Inner : for I in P_Prime.First .. P_Prime.Last loop
                  F(I) := P_Prime_Index;
                  pragma Loop_Invariant (for all K in Index range P_Prime.First .. I => F(K) = P_Prime_Index);
                  pragma Loop_Invariant (for all K in Index range 0 .. P_Prime.First - 1 => F(K) = F_Loop_Entry(K));
                  pragma Loop_Invariant (for all K in Index range I + 1 .. Index'Last => F(K) = F_Loop_Entry(K));
--                  pragma Loop_Invariant (for all K in Index => F(K) = (if K in P_Prime.First .. I then P_Prime_Index else F'Loop_Entry(K)));
               end loop Inner;

               --  Intermediate assertions to help with the proof of loop invariant F(K) in 0 .. Partition_Index'Base (Length (P)) - 1)
               pragma Assert (for all K in Index range P_Prime.First .. P_Prime.Last => F(K) = Partition_Index'Base (Length (P)) - 1);
               pragma Assert (for all K in Index range 0 .. P_Prime.First - 1 => F(K) in 0 .. Partition_Index'Base (Length (P)) - 1);
               pragma Assert (for all K in Index range P_Prime.Last + 1 .. Index'Last => F(K) in 0 .. Partition_Index'Base (Length (P)) - 1);

               --  Intermediate assertions to help with the proof of loop invariant K in Element (P, F(K)).First .. Element (P, F(K)).Last)
               pragma Assert (for all K in Index range P_Elem.First .. P_Elem.Last => Element (P, F(K)) = P_Elem);
               pragma Assert (for all K in Index range P_Elem.First .. P_Elem.Last => K in Element (P, F(K)).First .. Element (P, F(K)).Last);
               pragma Assert (for all K in Index range P_Prime.First .. P_Prime.Last => Element (P, F(K)) = P_Prime);
               pragma Assert (for all K in Index range P_Prime.First .. P_Prime.Last => K in Element (P, F(K)).First .. Element (P, F(K)).Last);
               pragma Assert (for all K in Index range 0 .. P_Elem.First - 1 => Element (P, F(K)) = Element (P_Save, F(K)));
               pragma Assert (for all K in Index range 0 .. P_Elem.First - 1 => K in Element (P_Save, F_Loop_Entry(K)).First .. Element (P_Save, F_Loop_Entry(K)).Last);
               pragma Assert (for all K in Index range 0 .. P_Elem.First - 1 => K in Element (P, F(K)).First .. Element (P, F(K)).Last);
               pragma Assert (for all K in Index range P_Prime.Last + 1 .. Index'Last => Element (P, F(K)) = Element (P_Save, F(K)));
               pragma Assert (for all K in Index range P_Prime.Last + 1 .. Index'Last => K in Element (P_Save, F_Loop_Entry(K)).First .. Element (P_Save, F_Loop_Entry(K)).Last);
               pragma Assert (for all K in Index range P_Prime.Last + 1 .. Index'Last => K in Element (P, F(K)).First .. Element (P, F(K)).Last);

               pragma Assert (for all K in 0 .. J - 1 => (for all L in Index range Element (P, K).First .. Element (P, K).Last => F(L) = K));
               pragma Assert (for all L in Index range Element (P, J).First .. Element (P, J).Last => F(L) = J);
               pragma Assert (for all K in J + 1 .. Partition_Index'Base (Length (P)) - 1 => (for all L in Index range Element (P, K).First .. Element (P, K).Last => F(L) = K));
            end;
         end if;

         --  Intermediate assertion used to decrease time to prove loop invariant
         pragma Assert (for all K in J + 1 .. Partition_Index'Base (Length (P)'Loop_Entry) - 1 => Element (P, K) = Element (P'Loop_Entry, K));

         pragma Assert (Capacity (P) = Capacity (P)'Loop_Entry);
         pragma Assert (Length (P) - Length (P)'Loop_Entry in 0 .. Count_Type(J) + 1);
         pragma Assert (for all K in J + 1 .. Partition_Index'Base (Length (P)'Loop_Entry) - 1 => Element (P, K) = Element (P'Loop_Entry, K));
         pragma Assert (for all K in Index => F(K) in 0 .. Partition_Index'Base (Length (P)) - 1);
         pragma Assert (for all K in Index => K in Element (P, F(K)).First .. Element (P, F(K)).Last);
         pragma Assert (for all K in 0 .. Partition_Index'Base (Length (P)) - 1 => (for all L in Index range Element (P, K).First .. Element (P, K).Last => F(L) = K));

         pragma Loop_Invariant (Capacity (P) = Capacity (P)'Loop_Entry);
         pragma Loop_Invariant (Length (P) - Length (P)'Loop_Entry in 0 .. Count_Type(J) + 1);
         pragma Loop_Invariant (for all K in J + 1 .. Partition_Index'Base (Length (P)'Loop_Entry) - 1 => Element (P, K) = Element (P'Loop_Entry, K));
         pragma Loop_Invariant (for all K in Index => F(K) in 0 .. Partition_Index'Base (Length (P)) - 1);
         pragma Loop_Invariant (for all K in Index => K in Element (P, F(K)).First .. Element (P, F(K)).Last);
         pragma Loop_Invariant (for all J in 0 .. Partition_Index'Base (Length (P)) - 1 => (for all K in Element (P, J).First .. Element (P, J).Last => F(K) = J));
      end loop;
   end Make_New_Partitions;

   ------------
   -- Refine --
   ------------

   procedure Refine
     (A : in out Set;
      D : in out Inverse_Set;
      P : in out Partition;
      F : in out Inverse_Partition;
      X : in     Partitioning_Set)
   is
      C : Partitioning_Sets.Cursor := First (X);

      pragma Warnings (Off, "statement has no effect", Reason => "ghost code");
      D_Old : constant Inverse_Set := D;
      pragma Warnings (On, "statement has no effect", Reason => "ghost code");

   begin
      while Has_Element (X, C) loop

         pragma Assert (Has_Element (D, (Find (D_Old, Element (X, C)))));
         --  This assumption is a logical consequence of the assertion above, that SPARK GPL 2014 does not prove.
         pragma Assume (Contains (D, Element (X, C)));
         Refine_One (A, D, P, F, Element (X, C));
         Next (X, C);

         --  P keeps its length and capacity through the loop
         pragma Loop_Invariant (Capacity (P) = Capacity (P)'Loop_Entry);
         pragma Loop_Invariant (Length (P) = Length (P)'Loop_Entry);
         --  D is the inverse map of A
         pragma Loop_Invariant (for all J in Index => Contains (D, A(J)));
         pragma Loop_Invariant (for all C in D => A (Element (D, C)) = Key (D, C));
         --  X is a subset of A
         pragma Loop_Invariant (for all C in D_Old => Has_Element (D, C));
         pragma Loop_Invariant (for all C in X => Has_Element (D, (Find (D_Old, Element (X, C)))));
         --  F maps indexes to their partition
         pragma Loop_Invariant (for all J in Index => F(J) in 0 .. Partition_Index'Base (Length (P)) - 1);
         pragma Loop_Invariant (for all J in Index => J in Element (P, F(J)).First .. Element (P, F(J)).Last);
         pragma Loop_Invariant (for all J in 0 .. Partition_Index'Base (Length (P)) - 1 => (for all K in Element (P, J).First .. Element (P, J).Last => F(K) = J));

         --  Uncomment loop variant to prove termination. It is commented because its presence causes GNATprove to fail to prove the loop invariant. But as the loop invariant is proved otherwise, we know it holds, thus the loop variant and invariant are both proved.
--       pragma Loop_Variant (Decreases => Length (Current_To_Last (X, C)));
      end loop;

      Make_New_Partitions (P, F);
   end Refine;

end Partition_Refinement;
