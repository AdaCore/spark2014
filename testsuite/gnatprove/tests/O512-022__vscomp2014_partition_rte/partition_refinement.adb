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
                --  (for all J in 0 .. Partition_Index(Length (P)) - 1 =>
                --     Element (P, J).First = Element (P'Old, J).First) and then
                --  (for all J in 0 .. Partition_Index(Length (P)) - 1 =>
                --     Element (P, J).Count = Element (P'Old, J).Count + (if J = F(Element (D'Old, X_Elem)) then 1 else 0)) and then
                (for all J in Index => Contains (D, A(J))) and then
                (for all C in D => A (Element (D, C)) = Key (D, C)) and then
                Keys (D)'Old = Keys (D);

   procedure Make_New_Partitions
     (P : in out Partition;
      F : in out Inverse_Partition)
   with
      Pre  => 2 * Length (P) <= Capacity (P) and then
              Length (P) <= Count_Type(Partition_Index'Last / 2);

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
      Replace_Element (P, F(I), P_Elem);

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
   begin
      for J in 0 .. Partition_Index'Base (Length (P)) - 1 loop

         --  Intermediate assertion used to decrease time to prove loop invariant
         --  pragma Assert (for all K in J .. Partition_Index'Base (Length (P)'Loop_Entry) - 1 => Element (P, K) = Element (P'Loop_Entry, K));

         pragma Loop_Invariant (Capacity (P) = Capacity (P)'Loop_Entry);
         pragma Loop_Invariant (Length (P) - Length (P)'Loop_Entry in 0 .. Count_Type(J));
         --  pragma Loop_Invariant (for all K in J .. Partition_Index'Base (Length (P)'Loop_Entry) - 1 => Element (P, K) = Element (P'Loop_Entry, K));
         P_Elem := Element (P, J);
         if P_Elem.Count in 1 .. P_Elem.Last - P_Elem.First then
            P_Prime := Interval'(First => P_Elem.First + P_Elem.Count,
                                 Last  => P_Elem.Last,
                                 Count => 0);
            P_Elem.Last := P_Elem.First + P_Elem.Count - 1;
            P_Elem.Count := 0;

            Replace_Element (P, J, P_Elem);
            P_Prime_Index := Partition_Index (Length (P));
            Append (P, P_Prime);

            for I in P_Prime.First .. P_Prime.Last loop
               F(I) := P_Prime_Index;
            end loop;
         end if;
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

--         pragma Assert (for all C in D_Old => Has_Element (D, C));
--         pragma Assert (Has_Element (D, (Find (D_Old, Element (X, C)))));
         --  This assumption is a logical consequence of the two assertion above, that SPARK GPL 2014 does not prove.
         pragma Assume (Contains (D, Element (X, C)));
         Refine_One (A, D, P, F, Element (X, C));
         Next (X, C);

         pragma Loop_Invariant (Capacity (P) = Capacity (P)'Loop_Entry);
         pragma Loop_Invariant (Length (P) = Length (P)'Loop_Entry);
         pragma Loop_Invariant (for all C in D => A (Element (D, C)) = Key (D, C));
--         pragma Loop_Invariant (for all C in D_Old => Has_Element (D, C));
--         pragma Loop_Invariant (for all C in X => Has_Element (D, (Find (D_Old, Element (X, C)))));
         pragma Loop_Invariant (for all C in X => Contains (D, Element (X, C)));
         pragma Loop_Invariant (for all J in Index => Contains (D, A(J)));

         pragma Loop_Variant (Increases =>
                                (if C = Partitioning_Sets.No_Element then Length (X)
                                 else Partitioning_Sets.Formal_Model.P.Get (Positions (X), C) - 1));
      end loop;

      Make_New_Partitions (P, F);
   end Refine;

end Partition_Refinement;
