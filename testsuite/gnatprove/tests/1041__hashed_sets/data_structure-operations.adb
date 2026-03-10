with SPARK.Cut_Operations; use SPARK.Cut_Operations;

package body Data_Structure.Operations
  with SPARK_Mode
is
   pragma Unevaluated_Use_Of_Old (Allow);

   package Private_Model
     with Ghost
   is

      use Memory_Index_Sequences;
      use Index_To_Value_Maps;
      use Basic_Model;

      --  Higher level model of a set

      --  Predicate: bucket B's entries appear at the correct positions
      --  within Allocated_Indexes.
      function Corresponding_Bucket
        (S : Set; B : Positive_Hash_Type; Allocated_Indexes : Sequence)
         return Boolean
      with
        Pre      => Basic_Model.LL_Invariant (S) and then B <= S.Modulus,
        Annotate => (GNATprove, Inline_For_Proof);

      function Corresponding_Bucket
        (S : Set; B : Positive_Hash_Type; Allocated_Indexes : Sequence)
         return Boolean
      is (Length (Allocated_Indexes) >= Num_Allocated (LL_Model (S).Buckets, B)
          and then
            (for all P in
               Interval'
                 (Num_Allocated (LL_Model (S).Buckets, B)
                  - Last (LL_Model (S).Buckets (B))
                  + 1,
                  Num_Allocated (LL_Model (S).Buckets, B)) =>
               Get (Allocated_Indexes, P)
               = Get
                   (LL_Model (S).Buckets (B),
                    Num_Allocated (LL_Model (S).Buckets, B) - P + 1))
          and then
            (for all P in Interval'(1, Last (LL_Model (S).Buckets (B))) =>
               Get (LL_Model (S).Buckets (B), P)
               = Get
                   (Allocated_Indexes,
                    Num_Allocated (LL_Model (S).Buckets, B) - P + 1)));

      --  Predicate: all buckets' entries appear correctly in Allocated_Indexes
      function Corresponding_Buckets
        (S : Set; Allocated_Indexes : Sequence) return Boolean
      with
        Pre      => Basic_Model.LL_Invariant (S),
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body");

      function Corresponding_Buckets
        (S : Set; Allocated_Indexes : Sequence) return Boolean
      is (for all B in 1 .. S.Modulus =>
            Corresponding_Bucket (S, B, Allocated_Indexes));

      --  The flat sequence of all allocated node indexes in bucket-then-
      --  reverse-position order.
      function HL_Allocated_Indexes (S : Set) return Sequence
      with
        Pre  => LL_Invariant (S),
        Post =>
          Length (HL_Allocated_Indexes'Result)
          = Num_Allocated (LL_Model (S).Buckets)
          and then Corresponding_Buckets (S, HL_Allocated_Indexes'Result)
          and then
            (for all I of HL_Allocated_Indexes'Result =>
               Has_Key (LL_Model (S).Values, I));
      --  Sequence of indexes allocated in S

      --  Proves Corresponding_Bucket holds for HL_Allocated_Indexes at
      --  bucket B.
      procedure Lemma_Corresponding_Bucket (S : Set; B : Positive_Hash_Type)
      with
        Pre  => LL_Invariant (S) and then B <= S.Modulus,
        Post => Corresponding_Bucket (S, B, HL_Allocated_Indexes (S));

      --  Lemmas relating properties on the low and high level models

      --  Proves Find(I) in the per-bucket LL structure agrees with Find(I)
      --  in the flat HL sequence.
      procedure Lemma_LL_Find_Is_HL_Find (S : Set; I : Positive_Count_Type)
      with
        Pre  => LL_Invariant (S),
        Post =>
          ((for all B in 1 .. S.Modulus =>
              Internal_Models.Find (LL_Model (S).Buckets (B), I) = 0)
           and Internal_Models.Find (HL_Allocated_Indexes (S), I) = 0)
          or else
            (Has_Key (LL_Model (S).Values, I)
             and
               Internal_Models.Find
                 (LL_Model (S).Buckets
                    (Find_Bucket (Get (LL_Model (S).Values, I), S.Modulus)),
                  I)
               > 0
             and Internal_Models.Find (HL_Allocated_Indexes (S), I) > 0
             and
               Internal_Models.Find (HL_Allocated_Indexes (S), I)
               = Num_Allocated
                   (LL_Model (S).Buckets,
                    Find_Bucket (Get (LL_Model (S).Values, I), S.Modulus))
                 - Internal_Models.Find
                     (LL_Model (S).Buckets
                        (Find_Bucket
                           (Get (LL_Model (S).Values, I), S.Modulus)),
                      I)
                 + 1);

      --  Proves element-based Find in the LL bucket structure agrees with
      --  the HL flat sequence.
      procedure Lemma_LL_Find_Is_HL_Find (S : Set; E : Element_Type)
      with
        Pre  => HL_Invariant (S),
        Post =>
          (Internal_Models.Find
             (LL_Model (S).Buckets (Find_Bucket (E, S.Modulus)),
              LL_Model (S).Values,
              E)
           = 0
           and
             Internal_Models.Find
               (HL_Allocated_Indexes (S), LL_Model (S).Values, E)
             = 0)
          or else
            (Internal_Models.Find
               (LL_Model (S).Buckets (Find_Bucket (E, S.Modulus)),
                LL_Model (S).Values,
                E)
             > 0
             and
               Internal_Models.Find
                 (HL_Allocated_Indexes (S), LL_Model (S).Values, E)
               > 0
             and
               Internal_Models.Find
                 (HL_Allocated_Indexes (S), LL_Model (S).Values, E)
               = Num_Allocated
                   (LL_Model (S).Buckets, Find_Bucket (E, S.Modulus))
                 - Internal_Models.Find
                     (LL_Model (S).Buckets (Find_Bucket (E, S.Modulus)),
                      LL_Model (S).Values,
                      E)
                 + 1);

      --  Relates the first non-empty bucket at or after B to the HL
      --  allocated-index sequence.
      procedure Lemma_First_Non_Empty_Bucket (S : Set; B : Positive_Hash_Type)
      with
        Pre  => B <= S.Modulus and then LL_Invariant (S),
        Post =>
          (declare
             B2 : constant Hash_Type :=
               (if (for all B2 in B .. S.Modulus =>
                      Length (LL_Model (S).Buckets (B2)) = 0)
                then S.Modulus
                else
                  Basic_Model.First_Non_Empty_Bucket (LL_Model (S).Buckets, B)
                  - 1);
             N  : constant Big_Natural :=
               (if B = 1
                then 0
                else Num_Allocated (LL_Model (S).Buckets, B - 1));
           begin
             (if B2 < S.Modulus
              then
                Length (HL_Model (S).Allocated_Indexes) > N
                and then
                  Get
                    (LL_Model (S).Buckets (B2 + 1),
                     Last (LL_Model (S).Buckets (B2 + 1)))
                  = Get (HL_Model (S).Allocated_Indexes, N + 1)
              else Length (HL_Model (S).Allocated_Indexes) = N));

      --  Proves two sets with identical bucket sequences have equal HL
      --  allocated-index sequences.
      procedure Lemma_HL_Eq (S, S_Old : Set)
      with
        Pre  =>
          LL_Invariant (S)
          and then LL_Invariant (S_Old)
          and then S.Modulus = S_Old.Modulus
          and then
            (for all B in 1 .. S.Modulus =>
               LL_Model (S_Old).Buckets (B) = LL_Model (S).Buckets (B)),
        Post => HL_Allocated_Indexes (S_Old) = HL_Allocated_Indexes (S);

      --  Proves that inserting node I into bucket B_New corresponds to an
      --  Is_Add on the HL sequences.
      procedure Lemma_HL_Is_Add
        (S_Old, S : Set; B_New : Positive_Hash_Type; I : Positive_Count_Type)
      with
        Pre  =>
          LL_Invariant (S)
          and then LL_Invariant (S_Old)
          and then S.Modulus = S_Old.Modulus
          and then B_New <= S.Modulus
          and then
            Is_Add
              (LL_Model (S_Old).Buckets (B_New),
               I,
               LL_Model (S).Buckets (B_New))
          and then
            (for all B in 1 .. S.Modulus =>
               (if B /= B_New
                then LL_Model (S_Old).Buckets (B) = LL_Model (S).Buckets (B))),
        Post =>
          Is_Add
            (HL_Allocated_Indexes (S_Old),
             Num_Allocated (LL_Model (S).Buckets, B_New)
             - Last (LL_Model (S).Buckets (B_New))
             + 1,
             I,
             HL_Allocated_Indexes (S));

      --  Proves that removing position Q_Old from bucket B_Old corresponds
      --  to an Is_Remove on the HL sequences.
      procedure Lemma_HL_Is_Remove
        (S_Old, S : Set; B_Old : Positive_Hash_Type; Q_Old : Big_Positive)
      with
        Pre  =>
          LL_Invariant (S)
          and then LL_Invariant (S_Old)
          and then S_Old.Modulus = S.Modulus
          and then B_Old <= S.Modulus
          and then Q_Old <= Length (LL_Model (S_Old).Buckets (B_Old))
          and then
            Is_Remove
              (LL_Model (S_Old).Buckets (B_Old),
               Q_Old,
               LL_Model (S).Buckets (B_Old))
          and then
            (for all B in 1 .. S.Modulus =>
               (if B /= B_Old
                then LL_Model (S_Old).Buckets (B) = LL_Model (S).Buckets (B))),
        Post =>
          Is_Remove
            (HL_Allocated_Indexes (S_Old),
             Num_Allocated (LL_Model (S_Old).Buckets, B_Old) - Q_Old + 1,
             HL_Allocated_Indexes (S));

      --  Proves that moving node I from B_Old to B_New corresponds to an
      --  Is_Move on the HL sequences.
      procedure Lemma_HL_Is_Move
        (S_Old, S     : Set;
         B_Old, B_New : Positive_Hash_Type;
         I            : Positive_Count_Type)
      with
        Ghost,
        Pre  =>
          LL_Invariant (S)
          and then LL_Invariant (S_Old)
          and then S.Modulus = S_Old.Modulus
          and then B_New <= S.Modulus
          and then B_Old <= S.Modulus
          and then B_Old /= B_New
          and then
            Internal_Models.Find (LL_Model (S_Old).Buckets (B_Old), I) > 0
          and then
            Is_Remove
              (LL_Model (S_Old).Buckets (B_Old),
               Internal_Models.Find (LL_Model (S_Old).Buckets (B_Old), I),
               LL_Model (S).Buckets (B_Old))
          and then
            Is_Add
              (LL_Model (S_Old).Buckets (B_New),
               I,
               LL_Model (S).Buckets (B_New))
          and then
            (for all B in 1 .. S.Modulus =>
               (if B /= B_New and B /= B_Old
                then LL_Model (S_Old).Buckets (B) = LL_Model (S).Buckets (B))),
        Post =>
          Is_Move
            (HL_Allocated_Indexes (S_Old),
             Num_Allocated (LL_Model (S_Old).Buckets, B_Old)
             - Internal_Models.Find (LL_Model (S_Old).Buckets (B_Old), I)
             + 1,
             Num_Allocated (LL_Model (S).Buckets, B_New)
             - Last (LL_Model (S).Buckets (B_New))
             + 1,
             HL_Allocated_Indexes (S));

      --  Lemmas used to prove element equivalence. We use functions so they
      --  can be used easily inside cut operations.

      --  Proves E1 and E2 are equivalent to each other, given both are
      --  equivalent to E.
      function Prove_Equivalent_Elements
        (E1, E2, E : Element_Type) return Boolean
      with
        Pre  => Equivalent_Elements (E1, E) and Equivalent_Elements (E2, E),
        Post =>
          Prove_Equivalent_Elements'Result and Equivalent_Elements (E1, E2);

   end Private_Model;
   use Private_Model;

   package body Advanced_Model is
      pragma Annotate (GNATprove, Unhide_Info, "package_body");

      function HL_Model (S : Set) return Set_HL_Model
      is ((Values            => LL_Model (S).Values,
           Allocated_Indexes => HL_Allocated_Indexes (S)));

      ------------------------------------
      -- Lemma_HL_No_Duplicated_Indexes --
      ------------------------------------

      procedure Lemma_HL_No_Duplicated_Indexes (S : Set) is
         M   : constant Set_LL_Model := LL_Model (S);
         R   : constant Sequence := HL_Allocated_Indexes (S);
         Lst : Big_Natural := Last (R);
      begin
         Basic_Model.Lemma_LL_No_Duplicated_Indexes (S);
         for B in reverse S.Buckets'Range loop
            Lemma_Corresponding_Bucket (S, B);
            pragma
              Loop_Invariant (Lst = Num_Allocated (LL_Model (S).Buckets, B));
            pragma
              Loop_Invariant
                (for all K in
                   Interval'(Lst - Last (M.Buckets (B)) + 1, Last (R)) =>
                   Has_Key (LL_Model (S).Values, Get (R, K)));
            pragma
              Loop_Invariant
                (for all K in
                   Interval'(Lst - Last (M.Buckets (B)) + 1, Last (R)) =>
                   Find_Bucket
                     (Get (LL_Model (S).Values, Get (R, K)), S.Modulus)
                   >= B);
            pragma
              Loop_Invariant
                (for all P1 in
                   Interval'(Lst - Last (M.Buckets (B)) + 1, Last (R)) =>
                   (for all P2 in Interval'(P1 + 1, Last (R)) =>
                      Get (R, P2) /= Get (R, P1)));
            Lst := Lst - Last (M.Buckets (B));
         end loop;
      end Lemma_HL_No_Duplicated_Indexes;

      --------------------------------
      -- Prove_Invariant_On_Default --
      --------------------------------

      procedure Prove_Invariant_On_Default (S : Set) is
      begin
         Basic_Model.Prove_Invariant_On_Default (S);
         if Default_Init (S) then
            declare
               HL : constant Sequence := HL_Allocated_Indexes (S);
            begin
               pragma Assert (if Default_Init (S) then Last (HL) = 0);
            end;
         end if;
      end Prove_Invariant_On_Default;

   end Advanced_Model;

   package body Private_Model is

      --------------------------
      -- HL_Allocated_Indexes --
      --------------------------

      function HL_Allocated_Indexes (S : Set) return Sequence is
         pragma
           Annotate
             (GNATprove,
              Unhide_Info,
              "Expression_Function_Body",
              Corresponding_Buckets);
         M : constant Set_LL_Model := LL_Model (S);
         I : Big_Integer;
      begin
         return R : Sequence do
            for B in S.Buckets'Range loop
               I := Last (M.Buckets (B));
               while I > 0 loop
                  R := Memory_Index_Sequences.Add (R, Get (M.Buckets (B), I));
                  pragma Loop_Variant (Decreases => I);
                  pragma Loop_Invariant (I > 0 and I <= Last (M.Buckets (B)));
                  pragma
                    Loop_Invariant
                      (Last (R)
                       = Last (R)'Loop_Entry + Last (M.Buckets (B)) - I + 1);
                  pragma
                    Loop_Invariant
                      (for all K in
                         Interval'(Last (R)'Loop_Entry + 1, Last (R)) =>
                         Get (R, K)
                         = Get
                             (M.Buckets (B),
                              Last (R)'Loop_Entry
                              + Last (M.Buckets (B))
                              - K
                              + 1));
                  pragma
                    Loop_Invariant
                      (for all K in Interval'(I, Last (M.Buckets (B))) =>
                         Get
                           (R,
                            Last (R)'Loop_Entry + Last (M.Buckets (B)) - K + 1)
                         = Get (M.Buckets (B), K));
                  pragma
                    Loop_Invariant (for all I of R => Has_Key (M.Values, I));
                  pragma
                    Loop_Invariant
                      (for all B2 in 1 .. B - 1 =>
                         Corresponding_Bucket (S, B2, R));
                  I := I - 1;
               end loop;
               pragma Assert (Corresponding_Bucket (S, B, R));
               pragma
                 Loop_Invariant (Length (R) = Num_Allocated (M.Buckets, B));
               pragma Loop_Invariant (for all I of R => Has_Key (M.Values, I));
               pragma
                 Loop_Invariant
                   (for all B2 in 1 .. B => Corresponding_Bucket (S, B2, R));
            end loop;
         end return;
      end HL_Allocated_Indexes;

      --------------------------------
      -- Lemma_Corresponding_Bucket --
      --------------------------------

      procedure Lemma_Corresponding_Bucket (S : Set; B : Positive_Hash_Type)
      is null;
      pragma
        Annotate
          (GNATprove,
           Unhide_Info,
           "Expression_Function_Body",
           Corresponding_Buckets);

      ----------------------------------
      -- Lemma_First_Non_Empty_Bucket --
      ----------------------------------

      procedure Lemma_First_Non_Empty_Bucket (S : Set; B : Positive_Hash_Type)
      is
         B2 : constant Hash_Type :=
           (if (for all B2 in B .. S.Modulus =>
                  Length (LL_Model (S).Buckets (B2)) = 0)
            then S.Modulus
            else
              Basic_Model.First_Non_Empty_Bucket (LL_Model (S).Buckets, B)
              - 1);
         N  : constant Big_Natural :=
           (if B = 1 then 0 else Num_Allocated (LL_Model (S).Buckets, B - 1));
      begin
         for K in B .. B2 loop
            pragma
              Loop_Invariant (Num_Allocated (LL_Model (S).Buckets, K) = N);
         end loop;
         if B > 0 then
            Lemma_Corresponding_Bucket (S, B);
         end if;
         if B2 < S.Modulus then
            Lemma_Corresponding_Bucket (S, B2 + 1);
         end if;
      end Lemma_First_Non_Empty_Bucket;

      -----------------
      -- Lemma_HL_Eq --
      -----------------

      procedure Lemma_HL_Eq (S, S_Old : Set) is
      begin
         for B in 1 .. S.Modulus loop
            Lemma_Corresponding_Bucket (S, B);
            Lemma_Corresponding_Bucket (S_Old, B);
            pragma
              Loop_Invariant
                (Num_Allocated (LL_Model (S).Buckets, B)
                 = Num_Allocated (LL_Model (S_Old).Buckets, B));
            pragma
              Loop_Invariant
                (for all P in
                   Interval'(1, Num_Allocated (LL_Model (S).Buckets, B)) =>
                   Get (HL_Model (S).Allocated_Indexes, P)
                   = Get (HL_Model (S_Old).Allocated_Indexes, P));
         end loop;
      end Lemma_HL_Eq;

      ---------------------
      -- Lemma_HL_Is_Add --
      ---------------------

      procedure Lemma_HL_Is_Add
        (S_Old, S : Set; B_New : Positive_Hash_Type; I : Positive_Count_Type)
      is
         P_New : constant Big_Positive :=
           Num_Allocated (LL_Model (S).Buckets, B_New)
           - Last (LL_Model (S).Buckets (B_New))
           + 1;
      begin
         for B in 1 .. S.Modulus loop
            Lemma_Corresponding_Bucket (S, B);
            Lemma_Corresponding_Bucket (S_Old, B);
            if B = B_New then
               pragma
                 Assert
                   (for all P in
                      Interval'(1, Num_Allocated (LL_Model (S).Buckets, B)) =>
                      (if P < P_New
                       then
                         Get (HL_Model (S).Allocated_Indexes, P)
                         = Get (HL_Model (S_Old).Allocated_Indexes, P)
                       elsif P > P_New
                       then
                         Get (HL_Model (S_Old).Allocated_Indexes, P - 1)
                         = Get (HL_Model (S).Allocated_Indexes, P)));
            end if;
            pragma
              Loop_Invariant
                (if B >= B_New
                 then Get (HL_Model (S).Allocated_Indexes, P_New) = I);
            pragma
              Loop_Invariant
                (if B >= B_New
                 then
                   Num_Allocated (LL_Model (S).Buckets, B) - 1
                   = Num_Allocated (LL_Model (S_Old).Buckets, B)
                 else
                   Num_Allocated (LL_Model (S).Buckets, B)
                   = Num_Allocated (LL_Model (S_Old).Buckets, B));
            pragma
              Loop_Invariant
                (if B >= B_New
                 then P_New <= Num_Allocated (LL_Model (S).Buckets, B));
            pragma
              Loop_Invariant
                (for all P in
                   Interval'(1, Num_Allocated (LL_Model (S).Buckets, B)) =>
                   (if B < B_New or (B >= B_New and P < P_New)
                    then
                      Get (HL_Model (S).Allocated_Indexes, P)
                      = Get (HL_Model (S_Old).Allocated_Indexes, P)));
            pragma
              Loop_Invariant
                (for all P in
                   Interval'(1, Num_Allocated (LL_Model (S).Buckets, B)) =>
                   (if B >= B_New and P > P_New
                    then
                      Get (HL_Model (S_Old).Allocated_Indexes, P - 1)
                      = Get (HL_Model (S).Allocated_Indexes, P)));
         end loop;
      end Lemma_HL_Is_Add;

      ----------------------
      -- Lemma_HL_Is_Move --
      ----------------------

      procedure Lemma_HL_Is_Move
        (S_Old, S     : Set;
         B_Old, B_New : Positive_Hash_Type;
         I            : Positive_Count_Type)
      is
         P_Old : constant Big_Positive :=
           Num_Allocated (LL_Model (S_Old).Buckets, B_Old)
           - Internal_Models.Find (LL_Model (S_Old).Buckets (B_Old), I)
           + 1;
         P_New : constant Big_Positive :=
           Num_Allocated (LL_Model (S).Buckets, B_New)
           - Last (LL_Model (S).Buckets (B_New))
           + 1;
      begin
         for B in 1 .. S.Modulus loop
            Lemma_Corresponding_Bucket (S, B);
            Lemma_Corresponding_Bucket (S_Old, B);
            if B = B_Old then
               pragma
                 Assert
                   (for all P in
                      Interval'(1, Num_Allocated (LL_Model (S).Buckets, B)) =>
                      (if P < P_Old and (B_Old < B_New or P < P_New)
                       then
                         Get (HL_Model (S).Allocated_Indexes, P)
                         = Get (HL_Model (S_Old).Allocated_Indexes, P)
                       elsif P > P_Old and B_Old > B_New and P > P_New
                       then
                         Get (HL_Model (S).Allocated_Indexes, P)
                         = Get (HL_Model (S_Old).Allocated_Indexes, P)
                       elsif B_Old < B_New
                       then
                         Get (HL_Model (S).Allocated_Indexes, P)
                         = Get (HL_Model (S_Old).Allocated_Indexes, P + 1)
                       elsif P > P_New
                       then
                         Get (HL_Model (S_Old).Allocated_Indexes, P - 1)
                         = Get (HL_Model (S).Allocated_Indexes, P)));
            end if;
            if B = B_New then
               pragma
                 Assert
                   (for all P in
                      Interval'(1, Num_Allocated (LL_Model (S).Buckets, B)) =>
                      (if (B_Old >= B_New or P < P_Old) and P < P_New
                       then
                         Get (HL_Model (S).Allocated_Indexes, P)
                         = Get (HL_Model (S_Old).Allocated_Indexes, P)
                       elsif P > P_Old and B_Old < B_New and P > P_New
                       then
                         Get (HL_Model (S).Allocated_Indexes, P)
                         = Get (HL_Model (S_Old).Allocated_Indexes, P)
                       elsif B_Old < B_New and P < P_New
                       then
                         Get (HL_Model (S).Allocated_Indexes, P)
                         = Get (HL_Model (S_Old).Allocated_Indexes, P + 1)
                       elsif P > P_New
                       then
                         Get (HL_Model (S_Old).Allocated_Indexes, P - 1)
                         = Get (HL_Model (S).Allocated_Indexes, P)));
            end if;
            pragma
              Loop_Invariant
                (if B >= B_New
                 then Get (HL_Model (S).Allocated_Indexes, P_New) = I);
            pragma
              Loop_Invariant
                (if B >= B_Old
                 then Get (HL_Model (S_Old).Allocated_Indexes, P_Old) = I);
            pragma
              Loop_Invariant
                (if B < B_New and B >= B_Old
                 then
                   Num_Allocated (LL_Model (S).Buckets, B)
                   = Num_Allocated (LL_Model (S_Old).Buckets, B) - 1
                 elsif B < B_Old and B >= B_New
                 then
                   Num_Allocated (LL_Model (S).Buckets, B) - 1
                   = Num_Allocated (LL_Model (S_Old).Buckets, B)
                 else
                   Num_Allocated (LL_Model (S).Buckets, B)
                   = Num_Allocated (LL_Model (S_Old).Buckets, B));
            pragma
              Loop_Invariant
                (if B >= B_Old
                 then P_Old <= Num_Allocated (LL_Model (S_Old).Buckets, B));
            pragma
              Loop_Invariant
                (if B >= B_New
                 then P_New <= Num_Allocated (LL_Model (S).Buckets, B));
            pragma
              Loop_Invariant
                (for all P in
                   Interval'(1, Num_Allocated (LL_Model (S).Buckets, B)) =>
                   (if B >= B_New
                      and P > P_New
                      and (B < B_Old or (B >= B_Old and P <= P_Old))
                    then
                      Get (HL_Model (S).Allocated_Indexes, P)
                      = Get (HL_Model (S_Old).Allocated_Indexes, P - 1)));
            pragma
              Loop_Invariant
                (for all P in
                   Interval'(1, Num_Allocated (LL_Model (S).Buckets, B)) =>
                   (if B >= B_Old
                      and P >= P_Old
                      and (B < B_New or (B >= B_New and P < P_New))
                    then
                      Get (HL_Model (S).Allocated_Indexes, P)
                      = Get (HL_Model (S_Old).Allocated_Indexes, P + 1)));
            pragma
              Loop_Invariant
                (for all P in
                   Interval'(1, Num_Allocated (LL_Model (S).Buckets, B)) =>
                   (if (B < B_Old or (B >= B_Old and P < P_Old))
                      and (B < B_New or (B >= B_New and P < P_New))
                    then
                      Get (HL_Model (S).Allocated_Indexes, P)
                      = Get (HL_Model (S_Old).Allocated_Indexes, P))
                   and
                     (if B >= B_Old and P > P_Old and B >= B_New and P > P_New
                      then
                        Get (HL_Model (S).Allocated_Indexes, P)
                        = Get (HL_Model (S_Old).Allocated_Indexes, P)));
         end loop;
      end Lemma_HL_Is_Move;

      ------------------------
      -- Lemma_HL_Is_Remove --
      ------------------------

      procedure Lemma_HL_Is_Remove
        (S_Old, S : Set; B_Old : Positive_Hash_Type; Q_Old : Big_Positive)
      is
         P_Old : constant Big_Positive :=
           Num_Allocated (LL_Model (S_Old).Buckets, B_Old) - Q_Old + 1;
      begin
         for B in 1 .. S.Modulus loop
            Lemma_Corresponding_Bucket (S, B);
            Lemma_Corresponding_Bucket (S_Old, B);
            if B = B_Old then
               pragma
                 Assert
                   (for all P in
                      Interval'(1, Num_Allocated (LL_Model (S).Buckets, B)) =>
                      (if P < P_Old
                       then
                         Get (HL_Model (S).Allocated_Indexes, P)
                         = Get (HL_Model (S_Old).Allocated_Indexes, P)
                       else
                         Get (HL_Model (S).Allocated_Indexes, P)
                         = Get (HL_Model (S_Old).Allocated_Indexes, P + 1)));
            end if;
            pragma
              Loop_Invariant
                (if B >= B_Old
                 then P_Old <= Num_Allocated (LL_Model (S_Old).Buckets, B));
            pragma
              Loop_Invariant
                (if B >= B_Old
                 then
                   Num_Allocated (LL_Model (S).Buckets, B)
                   = Num_Allocated (LL_Model (S_Old).Buckets, B) - 1
                 else
                   Num_Allocated (LL_Model (S).Buckets, B)
                   = Num_Allocated (LL_Model (S_Old).Buckets, B));
            pragma
              Loop_Invariant
                (for all P in
                   Interval'(1, Num_Allocated (LL_Model (S).Buckets, B)) =>
                   (if B < B_Old or (B >= B_Old and P < P_Old)
                    then
                      Get (HL_Model (S).Allocated_Indexes, P)
                      = Get (HL_Model (S_Old).Allocated_Indexes, P)));
            pragma
              Loop_Invariant
                (for all P in
                   Interval'(1, Num_Allocated (LL_Model (S).Buckets, B)) =>
                   (if B >= B_Old and P >= P_Old
                    then
                      Get (HL_Model (S).Allocated_Indexes, P)
                      = Get (HL_Model (S_Old).Allocated_Indexes, P + 1)));
         end loop;
      end Lemma_HL_Is_Remove;

      ------------------------------
      -- Lemma_LL_Find_Is_HL_Find --
      ------------------------------

      procedure Lemma_LL_Find_Is_HL_Find (S : Set; I : Positive_Count_Type) is
      begin
         for B in 1 .. S.Modulus loop
            Lemma_Corresponding_Bucket (S, B);
            if Internal_Models.Find (LL_Model (S).Buckets (B), I) > 0 then
               Lemma_HL_No_Duplicated_Indexes (S);
               Lemma_LL_No_Duplicated_Indexes (S);
               pragma
                 Assert
                   (Internal_Models.Find (HL_Allocated_Indexes (S), I) > 0);
               return;
            end if;
            pragma
              Loop_Invariant
                (for all B2 in 1 .. B =>
                   Internal_Models.Find (LL_Model (S).Buckets (B2), I) = 0);
            pragma
              Loop_Invariant
                (for all K in
                   Interval'(1, Num_Allocated (LL_Model (S).Buckets, B)) =>
                   Get (HL_Allocated_Indexes (S), K) /= I);
         end loop;
         pragma
           Assert
             (for all B in 1 .. S.Modulus =>
                Internal_Models.Find (LL_Model (S).Buckets (B), I) = 0);
         pragma
           Assert (Internal_Models.Find (HL_Allocated_Indexes (S), I) = 0);
      end Lemma_LL_Find_Is_HL_Find;

      ------------------------------
      -- Lemma_LL_Find_Is_HL_Find --
      ------------------------------

      procedure Lemma_LL_Find_Is_HL_Find (S : Set; E : Element_Type) is

         I : Big_Integer;
      begin
         Basic_Model.Lemma_LL_No_Duplicated_Indexes (S);
         for B in 1 .. S.Modulus loop
            Lemma_Corresponding_Bucket (S, B);
            if B = Find_Bucket (E, S.Modulus)
              and then
                Internal_Models.Find
                  (LL_Model (S).Buckets (B), LL_Model (S).Values, E)
                > 0
            then
               pragma
                 Assert
                   (Internal_Models.Find
                      (HL_Allocated_Indexes (S), LL_Model (S).Values, E)
                    > 0);

               pragma
                 Assert
                   (By
                      (Num_Allocated
                         (LL_Model (S).Buckets, Find_Bucket (E, S.Modulus))
                       - Internal_Models.Find
                           (LL_Model (S).Buckets (B), LL_Model (S).Values, E)
                       + 1
                       = Internal_Models.Find
                           (HL_Allocated_Indexes (S), LL_Model (S).Values, E),
                       Prove_Equivalent_Elements
                         (Get
                            (LL_Model (S).Values,
                             Get
                               (HL_Allocated_Indexes (S),
                                Num_Allocated (LL_Model (S).Buckets, B)
                                - Internal_Models.Find
                                    (LL_Model (S).Buckets (B),
                                     LL_Model (S).Values,
                                     E)
                                + 1)),
                          Get
                            (LL_Model (S).Values,
                             Get
                               (HL_Allocated_Indexes (S),
                                Internal_Models.Find
                                  (HL_Allocated_Indexes (S),
                                   LL_Model (S).Values,
                                   E))),
                          E)));
               return;
            else
               I := 1;
               while I <= Last (LL_Model (S).Buckets (B)) loop
                  Lemma_Equivalent_Elements_Find_Bucket
                    (Get
                       (LL_Model (S).Values,
                        Get (LL_Model (S).Buckets (B), I)),
                     E,
                     S.Modulus);
                  pragma
                    Loop_Variant
                      (Decreases => Last (LL_Model (S).Buckets (B)) - I);
                  pragma
                    Loop_Invariant
                      (I > 0 and I <= Last (LL_Model (S).Buckets (B)));
                  pragma
                    Loop_Invariant
                      (for all J in Interval'(1, I) =>
                         not Equivalent_Elements
                               (Get
                                  (LL_Model (S).Values,
                                   Get (LL_Model (S).Buckets (B), J)),
                                E));
                  I := I + 1;
               end loop;
            end if;
            pragma
              Loop_Invariant
                (for all B2 in 1 .. B =>
                   Internal_Models.Find
                     (LL_Model (S).Buckets (B2), LL_Model (S).Values, E)
                   = 0);
            pragma
              Loop_Invariant
                (for all K in
                   Interval'(1, Num_Allocated (LL_Model (S).Buckets, B)) =>
                   not Equivalent_Elements
                         (Get
                            (LL_Model (S).Values,
                             Get (HL_Allocated_Indexes (S), K)),
                          E));
         end loop;
      end Lemma_LL_Find_Is_HL_Find;

      -------------------------------
      -- Prove_Equivalent_Elements --
      -------------------------------

      function Prove_Equivalent_Elements
        (E1, E2, E : Element_Type) return Boolean is
      begin
         Lemma_Equivalent_Elements_Transitive (E1, E, E2);
         return True;
      end Prove_Equivalent_Elements;

   end Private_Model;
   use Basic_Model;

   ------------------------
   -- Conditional_Insert --
   ------------------------

   procedure Conditional_Insert
     (S        : in out Set;
      E        : Element_Type;
      I        : out Positive_Count_Type;
      Inserted : out Boolean)
   is
      S_Old : constant Set := S
      with Ghost;
      B     : constant Positive_Hash_Type := Find_Bucket (E, S.Modulus)
      with Ghost;

      procedure Prove_Post with Ghost is
         A_I   : constant Sequence := HL_Model (S).Allocated_Indexes;
         P_New : constant Big_Natural := Internal_Models.Find (A_I, I);
      begin
         Lemma_LL_Find_Is_HL_Find (S, I);
         if Inserted then
            Lemma_HL_Is_Add (S_Old, S, B, I);
         else
            Lemma_HL_Eq (S_Old, S);
         end if;
      end Prove_Post;
   begin
      Lemma_LL_Find_Is_HL_Find (S, E);
      Data_Structure.Basic_Operations.Conditional_Insert (S, E, I, Inserted);
      Prove_Post;
   end Conditional_Insert;

   --------------
   -- Contains --
   --------------

   function Contains (S : Set; E : Element_Type) return Boolean is
   begin
      Lemma_LL_Find_Is_HL_Find (S, E);
      return Data_Structure.Basic_Operations.Contains (S, E);
   end Contains;

   ------------
   -- Delete --
   ------------

   procedure Delete (S : in out Set; I : Positive_Count_Type) is
      S_Old : constant Set := S
      with Ghost;
      B     : constant Positive_Hash_Type :=
        Find_Bucket (Get (LL_Model (S).Values, I), S.Modulus)
      with Ghost;
   begin
      Lemma_LL_Find_Is_HL_Find (S, I);
      Lemma_HL_No_Duplicated_Indexes (S);
      Data_Structure.Basic_Operations.Delete (S, I);
      Lemma_HL_Is_Remove
        (S_Old, S, B, Internal_Models.Find (LL_Model (S_Old).Buckets (B), I));
   end Delete;

   ----------------
   -- Delete_Key --
   ----------------

   procedure Delete_Key (S : in out Set; E : Element_Type) is
      S_Old : constant Set := S
      with Ghost;
      B     : constant Positive_Hash_Type := Find_Bucket (E, S.Modulus)
      with Ghost;
      P     : constant Big_Natural :=
        Find (LL_Model (S_Old).Buckets (B), LL_Model (S_Old).Values, E)
      with Ghost;

      procedure Prove_Post with Ghost is
      begin
         if P = 0 then
            Lemma_HL_Eq (S_Old, S);
         else
            Lemma_HL_Is_Remove (S_Old, S, B, P);
            Lemma_LL_Find_Is_HL_Find (S, E);
         end if;
      end Prove_Post;
   begin
      Lemma_LL_Find_Is_HL_Find (S, E);
      Lemma_Corresponding_Bucket (S, B);
      Data_Structure.Basic_Operations.Delete_Key (S, E);
      Prove_Post;
      declare
         M     : constant Set_LL_Model := LL_Model (S)
         with Ghost;
         M_Old : constant Set_LL_Model := LL_Model (S_Old)
         with Ghost;
      begin
         pragma
           Assert
             (By
                (Find (M.Buckets (B), M.Values, E) = 0,
                 (if P = 0
                  then
                    (for all Q in Interval'(1, Last (M.Buckets (B))) =>
                       By
                         (not Equivalent_Elements
                                (Get (M.Values, Get (M.Buckets (B), Q)), E),
                          (if Equivalent_Elements
                                (Get (M.Values, Get (M.Buckets (B), Q)), E)
                           then
                             Prove_Equivalent_Elements
                               (Get (M_Old.Values, Get (M_Old.Buckets (B), Q)),
                                Get (M_Old.Values, Get (M_Old.Buckets (B), P)),
                                E)))))));
         Lemma_LL_Find_Is_HL_Find (S, E);
         pragma
           Assert_And_Cut (Find (HL_Allocated_Indexes (S), M.Values, E) = 0);
      end;
   end Delete_Key;

   -------------
   -- Element --
   -------------

   function Element (S : Set; I : Positive_Count_Type) return Element_Type is
   begin
      return Data_Structure.Basic_Operations.Element (S, I);
   end Element;

   ---------------
   -- Empty_Set --
   ---------------

   function Empty_Set (Capacity : Count_Type) return Set is
   begin
      return Data_Structure.Basic_Operations.Empty_Set (Capacity);
   end Empty_Set;

   ----------
   -- Find --
   ----------

   function Find (S : Set; E : Element_Type) return Count_Type is
   begin
      Lemma_LL_Find_Is_HL_Find (S, E);
      Lemma_Corresponding_Bucket (S, Find_Bucket (E, S.Modulus));
      return Data_Structure.Basic_Operations.Find (S, E);
   end Find;

   -----------
   -- First --
   -----------

   function First (S : Set) return Count_Type is
   begin
      Lemma_First_Non_Empty_Bucket (S, 1);
      return Data_Structure.Basic_Operations.First (S);
   end First;

   -----------------
   -- Has_Element --
   -----------------

   function Has_Element (S : Set; I : Positive_Count_Type) return Boolean
   with
     Refined_Post =>
       Has_Element'Result
       = (Internal_Models.Find (HL_Model (S).Allocated_Indexes, I) /= 0)
       and then Has_Element'Result = Basic_Operations.Has_Element (S, I)
   is
   begin
      Lemma_LL_Find_Is_HL_Find (S, I);
      return Data_Structure.Basic_Operations.Has_Element (S, I);
   end Has_Element;

   --------------
   -- Is_Empty --
   --------------

   function Is_Empty (S : Set) return Boolean is
   begin
      return Data_Structure.Basic_Operations.Is_Empty (S);
   end Is_Empty;

   ------------
   -- Length --
   ------------

   function Length (S : Set) return Count_Type is
   begin
      return Data_Structure.Basic_Operations.Length (S);
   end Length;

   ----------
   -- Next --
   ----------

   function Next (S : Set; I : Positive_Count_Type) return Count_Type is
      M : constant Set_LL_Model := LL_Model (S)
      with Ghost;

      procedure Prove_Post with Ghost is
         B : constant Positive_Hash_Type :=
           Find_Bucket (Get (M.Values, I), S.Modulus);
      begin
         Lemma_LL_Find_Is_HL_Find (S, I);
         if B < S.Modulus then
            Lemma_First_Non_Empty_Bucket (S, B + 1);
         end if;
         Lemma_Corresponding_Bucket (S, B);
      end Prove_Post;

   begin
      Prove_Post;
      return Data_Structure.Basic_Operations.Next (S, I);
   end Next;

   -------------
   -- Replace --
   -------------

   procedure Replace
     (S : in out Set; I : Positive_Count_Type; E : Element_Type)
   is
      S_Old : constant Set := S
      with Ghost;

      procedure Lemma_Prove_Post with Ghost is
         Old_A_I : constant Sequence := HL_Model (S_Old).Allocated_Indexes;
         A_I     : constant Sequence := HL_Model (S).Allocated_Indexes;
         P       : constant Big_Natural := Internal_Models.Find (A_I, I);
      begin
         pragma
           Assert
             (for all P1 in Interval'(1, Last (Old_A_I)) =>
                (if P1 /= Internal_Models.Find (Old_A_I, I)
                 then
                   By
                     (not Equivalent_Elements
                            (Get (HL_Model (S_Old).Values, Get (Old_A_I, P1)),
                             E),
                      (if Equivalent_Elements
                            (Get (HL_Model (S_Old).Values, Get (Old_A_I, P1)),
                             E)
                         and
                           Equivalent_Elements
                             (Get (HL_Model (S_Old).Values, I), E)
                       then
                         Prove_Equivalent_Elements
                           (Get (HL_Model (S_Old).Values, Get (Old_A_I, P1)),
                            Get (HL_Model (S_Old).Values, I),
                            E)))));
         Lemma_HL_No_Duplicated_Indexes (S_Old);
         Lemma_LL_Find_Is_HL_Find (S, I);
         Lemma_HL_Eq (S_Old, S);
      end Lemma_Prove_Post;
   begin
      Lemma_LL_Find_Is_HL_Find (S, E);
      Data_Structure.Basic_Operations.Replace (S, I, E);
      Lemma_Prove_Post;
   end Replace;

   ---------------------
   -- Replace_Element --
   ---------------------

   procedure Replace_Element
     (S : in out Set; I : Positive_Count_Type; E : Element_Type)
   is
      S_Old : constant Set := S
      with Ghost;
      B_Old : constant Positive_Hash_Type :=
        Find_Bucket (Get (HL_Model (S).Values, I), S.Modulus)
      with Ghost;
      B_New : constant Positive_Hash_Type := Find_Bucket (E, S.Modulus)
      with Ghost;

      procedure Lemma_Prove_Post with Ghost is
         Old_A_I : constant Sequence := HL_Model (S_Old).Allocated_Indexes;
         A_I     : constant Sequence := HL_Model (S).Allocated_Indexes;
         P       : constant Big_Natural := Internal_Models.Find (A_I, I);
      begin
         pragma
           Assert
             (for all P1 in Interval'(1, Last (Old_A_I)) =>
                (if P1 /= Internal_Models.Find (Old_A_I, I)
                 then
                   By
                     (not Equivalent_Elements
                            (Get (HL_Model (S_Old).Values, Get (Old_A_I, P1)),
                             E),
                      (if Equivalent_Elements
                            (Get (HL_Model (S_Old).Values, Get (Old_A_I, P1)),
                             E)
                         and
                           Equivalent_Elements
                             (Get (HL_Model (S_Old).Values, I), E)
                       then
                         Prove_Equivalent_Elements
                           (Get (HL_Model (S_Old).Values, Get (Old_A_I, P1)),
                            Get (HL_Model (S_Old).Values, I),
                            E)))));
         Lemma_HL_No_Duplicated_Indexes (S_Old);
         Lemma_LL_Find_Is_HL_Find (S, I);
         if B_Old = B_New then
            Lemma_HL_Eq (S_Old, S);
         else
            Lemma_LL_Find_Is_HL_Find (S_Old, I);
            Lemma_HL_Is_Move (S_Old, S, B_Old, B_New, I);
         end if;
      end Lemma_Prove_Post;
   begin
      Lemma_LL_Find_Is_HL_Find (S, E);
      Data_Structure.Basic_Operations.Replace_Element (S, I, E);
      Lemma_Prove_Post;
   end Replace_Element;

end Data_Structure.Operations;
