package body Stable_Marriage with SPARK_Mode is

   function Is_Permutation_1 (R1 : Ranking_Of_Group1) return Boolean is
      type Group1_Flags is array (Group1_Id) of Boolean;
      Seen : Group1_Flags := Group1_Flags'(others => False);
   begin
      for Rank in Ranking loop
         pragma Loop_Invariant
           (for all G1 in Group1_Id =>
              (Seen (G1) =
               (for some Prev in Ranking range 1 .. Rank - 1 =>
                    (R1 (Prev) = G1))));
         Seen (R1 (Rank)) := True;
      end loop;
      pragma Assert ((Seen = Group1_Flags'(others => True)) =
                     (for all G1 in Group1_Id => Seen (G1) and then
                        (for some Rank in Ranking =>
                           (R1 (Rank) = G1))));
      return Seen = Group1_Flags'(others => True);
   end Is_Permutation_1;

   procedure Invert_Permutation_1 (R1 : Ranking_Of_Group1) is null;

   function Is_Permutation_2 (R2 : Ranking_Of_Group2) return Boolean is
      type Group2_Flags is array (Group2_Id) of Boolean;
      Seen : Group2_Flags := Group2_Flags'(others => False);
   begin
      for Rank in Ranking loop
         pragma Loop_Invariant
           (for all G2 in Group2_Id =>
              (Seen (G2) =
               (for some Prev in Ranking range 1 .. Rank - 1 =>
                    (R2 (Prev) = G2))));
         Seen (R2 (Rank)) := True;
      end loop;
      pragma Assert ((Seen = Group2_Flags'(others => True)) =
                     (for all G2 in Group2_Id => Seen (G2) and then
                        (for some Rank in Ranking =>
                           (R2 (Rank) = G2))));
      return Seen = Group2_Flags'(others => True);
   end Is_Permutation_2;

   procedure Invert_Permutation_2 (R2 : Ranking_Of_Group2) is null;

   function Invert_1 (R1 : Ranking_Of_Group1)
                      return Inverted_Ranking_Of_Group1 is
      Result : Inverted_Ranking_Of_Group1 :=
        Inverted_Ranking_Of_Group1'(others => Last_Id);
      -- dead initial value
   begin
      Invert_Permutation_1 (R1);
      for Rank in Ranking loop
         pragma Loop_Invariant
           (for all Prev in Ranking range 1 .. Rank - 1 =>
              (Result (R1 (Prev)) = Prev));
         pragma Loop_Invariant
           (for all G1 in Group1_Id =>
              (if (for some Prev in Ranking range 1 .. Rank - 1 =>
                       R1 (Prev) = G1) then (R1 (Result (G1)) = G1)));
         Result (R1 (Rank)) := Rank;
      end loop;
      return Result;
   end Invert_1;

   function Invert_2 (R2 : Ranking_Of_Group2)
                      return Inverted_Ranking_Of_Group2 is
      Result : Inverted_Ranking_Of_Group2 :=
        Inverted_Ranking_Of_Group2'(others => Last_Id);
      -- dead initial value
   begin
      Invert_Permutation_2 (R2);
      for Rank in Ranking loop
         pragma Loop_Invariant
           (for all Prev in Ranking range 1 .. Rank - 1 =>
              (Result (R2 (Prev)) = Prev));
         pragma Loop_Invariant
           (for all G2 in Group2_Id =>
              (if (for some Prev in Ranking range 1 .. Rank - 1 =>
                       R2 (Prev) = G2) then (R2 (Result (G2)) = G2)));
         Result (R2 (Rank)) := Rank;
      end loop;
      return Result;
   end Invert_2;

   function Is_Preferred_1 (G1_A, G1_B : Group1_Id; R1 : Ranking_Of_Group1)
                            return Boolean is
      Inverted : Inverted_Ranking_Of_Group1;
   begin
      Inverted := Invert_1 (R1);
      return Inverted (G1_A) <= Inverted (G1_B);
   end Is_Preferred_1;

   function Is_Preferred_2 (G2_A, G2_B : Group2_Id; R2 : Ranking_Of_Group2)
                            return Boolean is
      Inverted : Inverted_Ranking_Of_Group2;
   begin
      Inverted := Invert_2 (R2);
      return Inverted (G2_A) <= Inverted (G2_B);
   end Is_Preferred_2;

   procedure Invert_Ranking_Of_Group_1 (G2_To_G1 : G2_To_G1_Map) is null;

   function Invert_Map (G2_To_G1 : G2_To_G1_Map) return G1_To_G2_Map is
      Result : G1_To_G2_Map := G1_To_G2_Map'(others => Last_Id);
      -- dead initial value
   begin
      Invert_Ranking_Of_Group_1 (G2_To_G1);
      for G2 in Group2_Id loop
         pragma Loop_Invariant
           (for all Prev in Group2_Id range 1 .. G2 - 1 =>
              (Result (G2_To_G1 (Prev)) = Prev));
         pragma Loop_Invariant
           (for all G1 in Group1_Id =>
              (if (for some Prev2 in Group2_Id range 1 .. G2 - 1 =>
                       (G2_To_G1 (Prev2) = G1)) then
                 (G2_To_G1 (Result (G1)) = G1)));
         Result (G2_To_G1 (G2)) := G2;
      end loop;
      return Result;
   end Invert_Map;

   type Inverted_Ranking is array (Group2_Id) of Inverted_Ranking_Of_Group1;

   function Invert (R2 : Ranking_Of_Group1_By_Group2)
                    return Inverted_Ranking with
     Pre => (for all G2 in Group2_Id =>
               Is_Permutation_1 (R2 (G2))),
     Post =>
       (for all G2 in Group2_Id =>
          (Invert'Result (G2) = Invert_1 (R2 (G2))))
   is
      Result : Inverted_Ranking;
   begin
      Result := Inverted_Ranking'(others =>
                                    Inverted_Ranking_Of_Group1'(others => (Last_Id)));
      -- dead assignment

      for G2 in Group2_Id loop
         pragma Loop_Invariant
           (for all Prev in Group2_Id range 1 .. G2 - 1 =>
              (Result (Prev) = Invert_1 (R2 (Prev))));
         Result (G2) := Invert_1 (R2 (G2));
      end loop;
      return Result;
   end Invert;

   function Matching
     (Ranking_1 : Ranking_Of_Group2_By_Group1;
      Ranking_2 : Ranking_Of_Group1_By_Group2)
      return G2_To_G1_Map is

      type Count is range 0 .. Last_Id;
      subtype Index is Count range 1 .. Last_Id;

      type Counts is array (Group1_Id) of Count;

      type Group1_Vector is array (Index) of Group1_Id;

      type Group1_Set is
         record
            Elements : Group1_Vector;
            Cardinality : Count;
         end record;

      type Group2_Set is array (Group2_Id) of Boolean;

      Ranking_2_Inverted : Inverted_Ranking;
      -- constant after initialization

      Proposals_Made : Counts := Counts'(others => 0);

      Unmatched_G1_Set : Group1_Set
        := Group1_Set'(Cardinality => 0,
                       Elements => Group1_Vector'(others => Last_Id));
      -- inital value of Elements is dead, but not init of Cardinality

      Unmatched_G2_Set : Group2_Set := Group2_Set'(others => True);
      -- initial value is live

      Result : G2_To_G1_Map := G2_To_G1_Map'(others => Last_Id);
      -- initial value is dead

      function All_Unmatched_G1_Set_Elements_Distinct return Boolean is
        (for all Idx_1 in Count range
           1 .. Unmatched_G1_Set.Cardinality =>
             (for all Idx_2 in Count range
                  1 .. Unmatched_G1_Set.Cardinality =>
                (if (Idx_1 /= Idx_2) then
                     (Unmatched_G1_Set.Elements (Idx_1) /=
                            Unmatched_G1_Set.Elements (Idx_2)))));

      function Invariant_Holds return Boolean
      is
        ((for all G2 in Group2_Id =>
            Is_Permutation_1 (Ranking_2 (G2))) and then

        (All_Unmatched_G1_Set_Elements_Distinct and


         -- for every G2, if G2 is matched with G1 then G1 is matched.

           (for all G2_Id in Group2_Id =>
                (if not Unmatched_G2_Set (G2_Id) then
                   (for all Idx in Count
                    range 1 .. Unmatched_G1_Set.Cardinality =>
                      (Unmatched_G1_Set.Elements (Idx)/= Result (G2_Id))))) and

           -- for every G2 is matched to a different person.

           (for all G21_Id in Group2_Id =>
                (for all G22_Id in Group2_Id =>
                     (if not Unmatched_G2_Set (G21_Id)
                      and not Unmatched_G2_Set (G22_Id)
                      and G21_Id /= G22_Id then
                         Result (G21_Id) /= Result (G22_Id)))) and


             -- for every G1, every G2 that the G1 has proposed to and
         -- been rejected by is matched with someone that the G2
         -- would not leave for this G1.

           (for all G1_Id in Group1_Id =>
                (for all Rank in Ranking range 1 ..
                     Ranking'Base (Proposals_Made (G1_Id)) =>
                   ((not Unmatched_G2_Set (Ranking_1 (G1_Id) (Rank))) and
                        (if Result (Ranking_1 (G1_Id) (Rank)) /= G1_Id then
                             not (Is_Preferred_1
                                  (G1_Id, Result (Ranking_1 (G1_Id) (Rank)),
                                   Ranking_2 (Ranking_1 (G1_Id) (Rank)))))))) and


         -- every G1 who has never proposed to anyone is in the
         -- unmatched pool

           (for all G1_Id in Group1_Id =>
                (if (Proposals_Made (G1_Id) = 0) then
                     (for some Idx in Count
                      range 1 .. Unmatched_G1_Set.Cardinality =>
                        (Unmatched_G1_Set.Elements (Idx) = G1_Id)))) and


           -- every G1 who is not in the unmatched pool is currently
         -- matched with their Rth choice, where R is the number
         -- of proposals this G1 has made.

           (for all G1_Id in Group1_Id =>
                (if (for all Idx in Count
                     range 1 .. Unmatched_G1_Set.Cardinality =>
                       (Unmatched_G1_Set.Elements (Idx)/= G1_Id)) then
                      Proposals_Made (G1_Id) > 0 and then
                   (Result (Ranking_1 (G1_Id)
                            (Ranking (Proposals_Made (G1_Id)))) = G1_Id)))));

      procedure Select_And_Remove_An_Unmatched_G1 (Selected : out Group1_Id)

        -- This procedure is over-specified. The algorithm should work if
        -- any element of the set is selected, not just the last element,
        -- but this would make the proofs more complex.
      is
      begin
         Selected :=
           Unmatched_G1_Set.Elements (Unmatched_G1_Set.Cardinality);
         Unmatched_G1_Set.Cardinality := Unmatched_G1_Set.Cardinality - 1;
      end Select_And_Remove_An_Unmatched_G1;

      procedure Add_An_Unmatched (New_Element : Group1_Id) is
      begin
         Unmatched_G1_Set.Cardinality := Unmatched_G1_Set.Cardinality + 1;
         Unmatched_G1_Set.Elements (Unmatched_G1_Set.Cardinality)
           := New_Element;
      end Add_An_Unmatched;

      procedure Make_One_Proposal with
        Pre  => (for all G2 in Group2_Id => Is_Permutation_1 (Ranking_2 (G2)))
        and then Invert (Ranking_2) = Ranking_2_Inverted
        and then Invariant_Holds and then Unmatched_G1_Set.Cardinality > 0,
        Post => Invariant_Holds

      -- Note that pre- and post- conditions are identical,
      -- which implies that this spec could be implemented by
      -- a null procedure. We are not trying to construct a
      -- termination proof at this point, so there is no need
      -- to prove that forward progress is being made at each
      -- iteration. One approach for proving termination is to
      -- note that the sum of all the Proposals_Made counts
      -- increases with each call to Make_One_Proposal, and
      -- that this sum cannot exceed Last_Id ** 2.

      is
         G1 : Group1_Id;
         G2 : Group2_Id;
         Accepted : Boolean;
         Rank : Ranking := Ranking'First;
         Already_Asked : Count;
      begin
         -- pragma Assert (Invariant_Holds);
         Select_And_Remove_An_Unmatched_G1 (G1);
         pragma Assert (Proposals_Made (G1) < Count'Last);

         Already_Asked := Proposals_Made (G1);
         if Already_Asked /= 0 then
            Rank := Ranking (Already_Asked) + 1;
            pragma Assert
              (not (Is_Preferred_1 (G1, Result (Ranking_1 (G1) (Rank - 1)),
               Ranking_2 (Ranking_1 (G1) (Rank - 1)))));
         end if;

         G2 := Ranking_1 (G1) (Rank);
         Proposals_Made (G1) := Proposals_Made (G1) + 1;

         if Unmatched_G2_Set (G2) then
            -- accept first proposal
            Accepted := True;
            Unmatched_G2_Set (G2) := False;
         elsif Ranking_2_Inverted (G2) (G1) <
           Ranking_2_Inverted (G2) (Result (G2)) then
            Accepted := True;
            -- previous match for G2 returns to Unmatched_G1_Set
            Add_An_Unmatched (Result (G2));
            pragma Assert (Is_Preferred_1 (G1, Result (G2), Ranking_2 (G2)));
         else
            -- G2 prefers current match to G1
            Accepted := False;
            Add_An_Unmatched (G1);
         end if;

         if Accepted then
            Result (G2):= G1;
         end if;

         pragma Assert (All_Unmatched_G1_Set_Elements_Distinct);

         pragma Assert
           (for all G21_Id in Group2_Id =>
              (for all G22_Id in Group2_Id =>
                   (if not Unmatched_G2_Set (G21_Id)
                    and not Unmatched_G2_Set (G22_Id)
                    and G21_Id /= G22_Id then
                       Result (G21_Id) /= Result (G22_Id))));

         pragma Assert
           (for all G2_Id in Group2_Id =>
              (if not Unmatched_G2_Set (G2_Id) then
                   (for all Idx in Count
                    range 1 .. Unmatched_G1_Set.Cardinality =>
                      (Unmatched_G1_Set.Elements (Idx)/= Result (G2_Id)))));

         pragma Assert
           (for all G1_Id in Group1_Id =>
              (for all Rank in Ranking range 1 ..
                   Ranking'Base (Proposals_Made (G1_Id)) =>
                 ((not Unmatched_G2_Set (Ranking_1 (G1_Id) (Rank))) and
                      (if Result (Ranking_1 (G1_Id) (Rank)) /= G1_Id then
                           not (Is_Preferred_1
                         (G1_Id, Result (Ranking_1 (G1_Id) (Rank)),
                            Ranking_2 (Ranking_1 (G1_Id) (Rank))))))));

         pragma Assert (for all G1_Id in Group1_Id =>
                          (if (Proposals_Made (G1_Id) = 0) then
                             (for some Idx in Count
                              range 1 .. Unmatched_G1_Set.Cardinality =>
                                (Unmatched_G1_Set.Elements (Idx) = G1_Id))));

         pragma Assert
           (for all G1_Id in Group1_Id =>
              (if (for all Idx in Count
               range 1 .. Unmatched_G1_Set.Cardinality =>
                 (Unmatched_G1_Set.Elements (Idx)/= G1_Id)) then
                    Proposals_Made (G1_Id) > 0 and then
                   (Result (Ranking_1 (G1_Id)
                    (Ranking (Proposals_Made (G1_Id)))) = G1_Id)));
      end Make_One_Proposal;

   begin
      Ranking_2_Inverted := Invert (Ranking_2);

      for G1 in Group1_Id loop
         pragma Loop_Invariant (Unmatched_G1_Set.Cardinality = Count (G1) - 1);
         pragma Loop_Invariant (All_Unmatched_G1_Set_Elements_Distinct);
         pragma Loop_Invariant
           (for all Prev in Count range 1 .. Count (G1) - 1 =>
                (Unmatched_G1_Set.Elements (Prev) = Group1_Id (Prev)));
         Add_An_Unmatched (G1);
      end loop;

      pragma Assert (All_Unmatched_G1_Set_Elements_Distinct);

      pragma Assert (for all G1_Id in Group1_Id =>
                       (Proposals_Made (G1_Id) = 0 and
                          (Unmatched_G1_Set.Elements (Count (G1_Id)) = G1_Id)));

      while Unmatched_G1_Set.Cardinality > 0 loop
         pragma Loop_Invariant (Invariant_Holds);
         Make_One_Proposal;
      end loop;

      return Result;
   end Matching;

end Stable_Marriage;
