with SPARK.Big_Intervals;  use SPARK.Big_Intervals;
with SPARK.Cut_Operations; use SPARK.Cut_Operations;

package body Data_Structure.Basic_Operations
  with SPARK_Mode
is

   package Private_Model
     with Ghost
   is

      package Memory_Index_Sets is new
        SPARK.Containers.Functional.Sets (Positive_Count_Type);
      use Memory_Index_Sets;
      subtype Memory_Index_Set is Memory_Index_Sets.Set;

      --  Special set constants used in specifications

      function Empty_Set return Memory_Index_Set
      with
        Post =>
          Length (Empty_Set'Result) = 0
          and then (for all I in Positive_Count_Type =>
                      not Contains (Empty_Set'Result, I));
      function All_Set (Capacity : Count_Type) return Memory_Index_Set
      with
        Post =>
          Length (All_Set'Result) = To_Big (Capacity)
          and then (for all I in 1 .. Capacity => Contains (All_Set'Result, I))
          and then (for all E of All_Set'Result => E <= Capacity);

      --  The list starting at X in M represents an acyclic list

      function Well_Formed (X : Count_Type; M : Memory_Type) return Boolean
      with
        Pre      => X <= M'Last,
        Post     => (if X = 0 then Well_Formed'Result),
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body");

      procedure Lemma_Well_Formed_Def (X : Positive_Count_Type; M : Memory_Type)
      with
        Pre  => X <= M'Last,
        Post => Well_Formed (X, M) = Well_Formed (M (X).Next, M);

      procedure Lemma_Well_Formed_Preserved
        (X : Count_Type; M1, M2 : Memory_Type)
      with
        Pre  =>
          X <= M1'Last
          and then M1'Last = M2'Last
          and then (for all I of Reachable_Set (X, M1) =>
                      M1 (I).Next = M2 (I).Next),
        Post => Well_Formed (X, M1) = Well_Formed (X, M2);

      procedure Lemma_Well_Formed_Set
        (X, Y : Positive_Count_Type; Z : Count_Type; M1, M2 : Memory_Type)
      with
        Subprogram_Variant => (Decreases => Length (Reachable_Set (X, M1))),
        Pre                =>
          M1'Last = M2'Last
          and then X <= M1'Last
          and then Y <= M1'Last
          and then Z <= M1'Last
          and then M2 (Y).Next = Z
          and then (for all K in M1'Range =>
                      (if K /= Y then M2 (K).Next = M1 (K).Next))
          and then Well_Formed (X, M1)
          and then Well_Formed (Z, M1)
          and then Reachable (X, M1, Y)
          and then not Reachable (Z, M1, Y),
        Post               => Well_Formed (X, M2);

      --  The set of reachable memory indexes from X in M

      function Reachable_Set
        (X : Count_Type; M : Memory_Type) return Memory_Index_Set
      with
        Pre      => X <= M'Last,
        Post     =>
          (if X = 0
           then Is_Empty (Reachable_Set'Result)
           else Contains (Reachable_Set'Result, X))
          and then Length (Reachable_Set'Result) <= To_Big (M'Last)
          and then (for all I of Reachable_Set'Result => I in M'Range),
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body");

      procedure Lemma_Reachable_Def (X : Positive_Count_Type; M : Memory_Type)
      with
        Pre  => X <= M'Last and then Well_Formed (X, M),
        Post =>
          not Contains (Reachable_Set (M (X).Next, M), X)
          and then Reachable_Set (X, M) = Add (Reachable_Set (M (X).Next, M), X)
          and then Length (Reachable_Set (X, M))
                   = 1 + Length (Reachable_Set (M (X).Next, M));

      procedure Lemma_Reachable_Preserved (X : Count_Type; M1, M2 : Memory_Type)
      with
        Pre  =>
          M1'Last = M2'Last
          and then X <= M1'Last
          and then (for all I of Reachable_Set (X, M1) =>
                      M1 (I).Next = M2 (I).Next),
        Post =>
          Reachable_Set (X, M1) = Reachable_Set (X, M2)
          and then Length (Reachable_Set (X, M1))
                   = Length (Reachable_Set (X, M2));

      procedure Lemma_Reachable_Set
        (X, Y : Positive_Count_Type; Z : Count_Type; M1, M2 : Memory_Type)
      with
        Subprogram_Variant => (Decreases => Length (Reachable_Set (X, M1))),
        Pre                =>
          M1'Last = M2'Last
          and then X <= M1'Last
          and then Y <= M1'Last
          and then Z <= M1'Last
          and then M2 (Y).Next = Z
          and then (for all K in M1'Range =>
                      (if K /= Y then M2 (K).Next = M1 (K).Next))
          and then Well_Formed (X, M1)
          and then Well_Formed (Z, M1)
          and then Reachable (X, M1, Y)
          and then not Reachable (Z, M1, Y),
        Post               =>
          (for all I of Reachable_Set (X, M2) =>
             Reachable (Z, M1, I)
             or else (Reachable (X, M1, I)
                      and then not Reachable (M1 (Y).Next, M1, I)))
          and then (for all I of Reachable_Set (Z, M1) => Reachable (X, M2, I))
          and then (for all I of Reachable_Set (X, M1) =>
                      Reachable (X, M2, I)
                      or else Reachable (M1 (Y).Next, M1, I));

      function Reachable
        (X : Count_Type; M : Memory_Type; Y : Positive_Count_Type)
         return Boolean
      is (Contains (Reachable_Set (X, M), Y))
      with
        Pre      => X <= M'Last and then Y <= M'Last,
        Annotate => (GNATprove, Inline_For_Proof);

      --  Invariant: The buckets and free lists are well formed and they do not overlap

      function LL_Correct_Well_Formed_Buckets (S : Set) return Boolean
      is (for all B1 in S.Buckets'Range =>
            Well_Formed (S.Buckets (B1), S.Memory));

      function LL_Correct_Buckets_Value (S : Set) return Boolean
      is ((for all B in S.Buckets'Range =>
             (for all I of Reachable_Set (S.Buckets (B), S.Memory) =>
                S.Memory (I).Value'Initialized))
          and then (for all B in S.Buckets'Range =>
                      (for all I of Reachable_Set (S.Buckets (B), S.Memory) =>
                         Find_Bucket (S.Memory (I).Value.V, S.Modulus) = B)));

      function LL_Correct_Free_List (S : Set) return Boolean
      is ((if S.Free >= 0 then Well_Formed (S.Free, S.Memory))
          and then (if S.Free >= 0
                    then
                      (for all I of Reachable_Set (S.Free, S.Memory) =>
                         (for all B in S.Buckets'Range =>
                            not Reachable (S.Buckets (B), S.Memory, I)))
                    else
                      (for all I in -S.Free .. S.Capacity =>
                         (for all B in S.Buckets'Range =>
                            not Reachable (S.Buckets (B), S.Memory, I)))));

      function Values_From_Memory_Buckets
        (S : Set; Values : Values_Type) return Boolean
      is ((for all I of Values =>
             I <= S.Capacity
             and then Reachable
                        (S.Buckets (Find_Bucket (Get (Values, I), S.Modulus)),
                         S.Memory,
                         I))
          and then (for all B in S.Buckets'Range =>
                      (for all I of Reachable_Set (S.Buckets (B), S.Memory) =>
                         Has_Key (Values, I))))
      with Annotate => (GNATprove, Hide_Info, "Expression_Function_Body");

      function Values_From_Memory_Values
        (S : Set; Values : Values_Type) return Boolean
      is ((for all I of Values =>
             I <= S.Capacity and then S.Memory (I).Value'Initialized)
          and then (for all I of Values =>
                      S.Memory (I).Value.V = Get (Values, I)));

      function Values_From_Memory (S : Set) return Values_Type
      with
        Pre  =>
          LL_Correct_Well_Formed_Buckets (S)
          and then LL_Correct_Buckets_Value (S),
        Post =>
          Values_From_Memory_Buckets (S, Values_From_Memory'Result)
          and then Values_From_Memory_Values (S, Values_From_Memory'Result);
      --  Construct the value map from memory

      procedure Lemma_Values_Buckets
        (S : Set; B : Positive_Hash_Type; I : Positive_Count_Type)
      with
        Pre  =>
          LL_Correct_Well_Formed_Buckets (S)
          and then LL_Correct_Buckets_Value (S)
          and then B <= S.Modulus
          and then I <= S.Capacity,
        Post =>
          (if Reachable (S.Buckets (B), S.Memory, I)
           then Has_Key (Values_From_Memory (S), I))
          and (if Has_Key (Values_From_Memory (S), I)
                 and then B = Find_Bucket (S.Memory (I).Value.V, S.Modulus)
               then Reachable (S.Buckets (B), S.Memory, I));

      procedure Lemma_Values_Preserved (S1, S2 : Set; I : Count_Type := 0)
      with
        Pre  =>
          LL_Correct_Well_Formed_Buckets (S1)
          and then LL_Correct_Buckets_Value (S1)
          and then LL_Correct_Well_Formed_Buckets (S2)
          and then LL_Correct_Buckets_Value (S2)
          and then I <= S1.Capacity
          and then S1.Capacity = S2.Capacity
          and then S1.Modulus = S2.Modulus
          and then (for all B in 1 .. S1.Modulus =>
                      (for all J in 1 .. S1.Capacity =>
                         (if I /= J
                          then
                            Contains
                              (Reachable_Set (S1.Buckets (B), S1.Memory), J)
                            = Contains
                                (Reachable_Set (S2.Buckets (B), S2.Memory),
                                 J))))
          and then (for all B in 1 .. S1.Modulus =>
                      (for all J of Reachable_Set (S1.Buckets (B), S1.Memory) =>
                         (if I /= J
                          then S1.Memory (J).Value.V = S2.Memory (J).Value.V))),
        Post =>
          (for all J of Values_From_Memory (S1) =>
             (if I /= J then Has_Key (Values_From_Memory (S2), J)))
          and then (for all J of Values_From_Memory (S2) =>
                      (if I /= J then Has_Key (Values_From_Memory (S1), J)))
          and then (for all J of Values_From_Memory (S2) =>
                      (if I /= J
                       then
                         Get (Values_From_Memory (S1), J)
                         = Get (Values_From_Memory (S2), J)));

      --  Invariant: The buckets and free lists cover the whole memory

      function Is_Allocated
        (Buckets : Bucket_Array; M : Memory_Type; I : Positive_Count_Type)
         return Boolean
      is (M (I).Value'Initialized
          and then Reachable
                     (Buckets (Find_Bucket (M (I).Value.V, Buckets'Last)),
                      M,
                      I))
      with
        Pre =>
          I <= M'Last
          and then Buckets'Last >= 1
          and then (for all B of Buckets => B <= M'Last);

      function Is_Free
        (Free : Count_Type'Base; M : Memory_Type; I : Positive_Count_Type)
         return Boolean
      is (if Free >= 0 then Reachable (Free, M, I) else I >= -Free)
      with Pre => I <= M'Last and then Free in -M'Last .. M'Last;

      function LL_Complete (S : Set) return Boolean
      is (for all I in S.Memory'Range =>
            Is_Free (S.Free, S.Memory, I)
            or else Is_Allocated (S.Buckets, S.Memory, I));

      --  Invariant: The Has_Element field of each cell is set iff the cell is allocated

      function LL_Has_Element (S : Set) return Boolean
      is (for all I in S.Memory'Range =>
            Is_Allocated (S.Buckets, S.Memory, I) = S.Memory (I).Has_Element);

      --  Invariant: The Length component is the number of allocated cells

      function Num_Allocated
        (Buckets : Bucket_Array; M : Memory_Type; B : Hash_Type)
         return Big_Natural
      with
        Subprogram_Variant => (Decreases => B),
        Pre                =>
          B in Buckets'Range
          and then Buckets'Last >= 1
          and then (for all B of Buckets => B <= M'Last);

      function Num_Allocated
        (Buckets : Bucket_Array; M : Memory_Type; B : Hash_Type)
         return Big_Natural
      is (Length (Reachable_Set (Buckets (B), M))
          + (if B = 1 then 0 else Num_Allocated (Buckets, M, B - 1)));

      function Num_Allocated (S : Set) return Big_Natural
      is (Num_Allocated (S.Buckets, S.Memory, S.Modulus));

      procedure Lemma_Length_Complete (S : Set)
      with
        Ghost,
        Pre  => LL_Correct (S) and LL_Complete (S),
        Post =>
          (if S.Free >= 0
           then
             Num_Allocated (S)
             = To_Big (S.Capacity) - Length (Reachable_Set (S.Free, S.Memory))
           else Num_Allocated (S) = To_Big (-S.Free - 1));

      function LL_Length (S : Set) return Boolean
      is (To_Big (S.Length) = Num_Allocated (S));

      --  Special sequences used in specifications

      function Empty_Seq return Sequence
      with Post => Length (Empty_Seq'Result) = 0;

      function All_From_Seq (Fst, Lst : Count_Type) return Sequence
      with
        Pre  => Fst <= Lst,
        Post =>
          Length (All_From_Seq'Result) = To_Big (Lst - Fst)
          and then (for all I in Interval'(1, To_Big (Lst - Fst)) =>
                      To_Big (Get (All_From_Seq'Result, I))
                      = To_Big (Lst) - I + 1);

      function LL_Sequence (X : Count_Type; M : Memory_Type) return Sequence
      with
        Pre      => X <= M'Last and then Well_Formed (X, M),
        Post     =>
          Length (LL_Sequence'Result) = Length (Reachable_Set (X, M))
          and then (for all I of LL_Sequence'Result =>
                      Contains (Reachable_Set (X, M), I))
          and then (if X = 0
                    then Length (LL_Sequence'Result) = 0
                    else
                      In_Range (Length (LL_Sequence'Result), 1, To_Big (M'Last))
                      and then Get
                                 (LL_Sequence'Result, Last (LL_Sequence'Result))
                               = X),
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body");

      procedure Lemma_LL_Sequence_Def (X : Count_Type; M : Memory_Type)
      with
        Pre  => X <= M'Last and then Well_Formed (X, M),
        Post =>
          --  Resursive definition
          (if X = 0
           then Length (LL_Sequence (X, M)) = 0
           else Is_Add (LL_Sequence (M (X).Next, M), X, LL_Sequence (X, M)));

      procedure Lemma_LL_Sequence_Preserved
        (X : Count_Type; M1, M2 : Memory_Type)
      with
        Ghost,
        Subprogram_Variant => (Decreases => Length (Reachable_Set (X, M1))),
        Pre                =>
          M1'Last = M2'Last
          and then X <= M1'Last
          and then Well_Formed (X, M1)
          and then (for all I of Reachable_Set (X, M1) =>
                      M1 (I).Next = M2 (I).Next),
        Post               => LL_Sequence (X, M1) = LL_Sequence (X, M2);

      procedure Lemma_LL_Sequence_Set
        (X, Y : Positive_Count_Type; Z : Count_Type; M1, M2 : Memory_Type)
      with
        Ghost,
        Subprogram_Variant => (Decreases => Length (Reachable_Set (X, M1))),
        Pre                =>
          M1'Last = M2'Last
          and then X <= M1'Last
          and then Y <= M1'Last
          and then Z <= M1'Last
          and then M2 (Y).Next = Z
          and then (for all K in M1'Range =>
                      (if K /= Y then M2 (K).Next = M1 (K).Next))
          and then Well_Formed (X, M1)
          and then Well_Formed (Z, M1)
          and then Reachable (X, M1, Y)
          and then not Reachable (Z, M1, Y),
        Post               =>
          LL_Sequence (Z, M1) <= LL_Sequence (X, M2)
          and Length (LL_Sequence (X, M2))
              = Length (LL_Sequence (X, M1))
                - Length (LL_Sequence (Y, M1))
                + Length (LL_Sequence (Z, M1))
                + 1
          and Range_Shifted
                (LL_Sequence (X, M2),
                 LL_Sequence (X, M1),
                 Last (LL_Sequence (Z, M1)) + 1,
                 Last (LL_Sequence (X, M2)),
                 Length (LL_Sequence (Y, M1))
                 - Length (LL_Sequence (Z, M1))
                 - 1);

      function LL_Free (S : Set) return Sequence
      is (if S.Free < 0
          then All_From_Seq (-S.Free - 1, S.Capacity)
          else LL_Sequence (S.Free, S.Memory))
      with Pre => (if S.Free >= 0 then Well_Formed (S.Free, S.Memory));

      function Find
        (M : Memory_Type; Fst : Count_Type; I : Positive_Count_Type)
         return Big_Natural
      with
        Pre  =>
          Fst <= M'Last and then I <= M'Last and then Well_Formed (Fst, M),
        Post =>
          Find'Result <= Last (LL_Sequence (Fst, M))
          and then (if Find'Result > 0
                    then Get (LL_Sequence (Fst, M), Find'Result) = I)
          and then (for all K in
                      Interval'(Find'Result + 1, Last (LL_Sequence (Fst, M))) =>
                      Get (LL_Sequence (Fst, M), K) /= I)
          and then (if Reachable (Fst, M, I) then Find'Result /= 0);

      function Find
        (M : Memory_Type; Fst : Count_Type; E : Element_Type) return Big_Natural
      with
        Pre  =>
          Fst <= M'Last
          and then Well_Formed (Fst, M)
          and then (for all I of Reachable_Set (Fst, M) =>
                      M (I).Value'Initialized),
        Post =>
          Find'Result <= Last (LL_Sequence (Fst, M))
          and then (if Find'Result > 0
                    then
                      Equivalent_Elements
                        (M (Get (LL_Sequence (Fst, M), Find'Result)).Value.V,
                         E))
          and then (for all K in
                      Interval'(Find'Result + 1, Last (LL_Sequence (Fst, M))) =>
                      not Equivalent_Elements
                            (M (Get (LL_Sequence (Fst, M), K)).Value.V, E));

      procedure Lemma_LL_Sequence_No_Duplicated_Indexes (S : Set; B : Hash_Type)
      with
        Pre  => LL_Correct (S) and then B in 1 .. S.Modulus,
        Post => No_Duplicated_Indexes (LL_Sequence (S.Buckets (B), S.Memory));
   end Private_Model;
   use Private_Model;

   package body Basic_Model is
      pragma Annotate (GNATprove, Unhide_Info, "Package_Body");

      function LL_Correct (S : Set) return Boolean
      is (LL_Correct_Free_List (S)
          and then LL_Correct_Well_Formed_Buckets (S)
          and then LL_Correct_Buckets_Value (S));

      function LL_Invariant (S : Set) return Boolean
      is (LL_Correct (S)
          and then LL_Complete (S)
          and then LL_Has_Element (S)
          and then LL_Length (S));

      function LL_Buckets (S : Set) return Mem_Seq_Array
      is (for B in 1 .. S.Modulus => LL_Sequence (S.Buckets (B), S.Memory))
      with Pre => LL_Correct (S);

      function LL_Model (S : Set) return Set_LL_Model
      is ((Capacity => S.Capacity,
           Modulus  => S.Modulus,
           Values   => Values_From_Memory (S),
           Buckets  => LL_Buckets (S)));
      pragma
        Annotate
          (GNATprove,
           Unhide_Info,
           "Expression_Function_Body",
           Values_From_Memory_Buckets);

      function First_Non_Empty_Bucket
        (Buckets : Mem_Seq_Array; B : Positive_Hash_Type)
         return Positive_Hash_Type is
      begin
         for B_N in B .. Buckets'Last loop
            if Length (Buckets (B_N)) /= 0 then
               return B_N;
            end if;
            pragma
              Loop_Invariant
                (for all B_2 in B .. B_N => Length (Buckets (B_2)) = 0);
         end loop;
         raise Program_Error;
      end First_Non_Empty_Bucket;

      procedure Lemma_LL_No_Duplicated_Indexes (S : Set) is
         pragma
           Annotate
             (GNATprove,
              Hide_Info,
              "Expression_Function_Body",
              LL_Correct_Free_List);
      begin
         for B in S.Buckets'Range loop
            Lemma_LL_Sequence_No_Duplicated_Indexes (S, B);
            pragma
              Loop_Invariant
                (for all K in 1 .. B =>
                   No_Duplicated_Indexes
                     (LL_Sequence (S.Buckets (K), S.Memory)));
         end loop;
      end Lemma_LL_No_Duplicated_Indexes;

   end Basic_Model;

   package body Private_Model is
      pragma Annotate (GNATprove, Unhide_Info, "Package_Body");
      --  Local functions

      function LL_Sequence_Internal
        (X : Count_Type; M : Memory_Type) return Sequence
      with
        Subprogram_Variant => (Decreases => Length (Reachable_Set (X, M))),
        Pre                => X <= M'Last and then Well_Formed (X, M),
        Post               =>
          --  Resursive definition
          (if X = 0
           then Length (LL_Sequence_Internal'Result) = 0
           else
             Is_Add
               (LL_Sequence_Internal (M (X).Next, M),
                X,
                LL_Sequence_Internal'Result))
          --  Relation with reachable sets
          and then Length (LL_Sequence_Internal'Result)
                   = Length (Reachable_Set (X, M))
          and then (for all I of LL_Sequence_Internal'Result =>
                      Contains (Reachable_Set (X, M), I))
          and then (for all I of LL_Sequence_Internal'Result => I <= M'Last);

      function Reachable_Set_Internal
        (X : Count_Type; M : Memory_Type; S : Memory_Index_Set)
         return Memory_Index_Set
      with
        Subprogram_Variant => (Decreases => Length (S)),
        Pre                => X <= M'Last,
        Post               =>
          Reachable_Set_Internal'Result <= S
          and Length (Reachable_Set_Internal'Result) <= Length (S)
          and (for all I of Reachable_Set_Internal'Result => I in M'Range);

      function Well_Formed_Internal
        (X : Count_Type; M : Memory_Type; S : Memory_Index_Set) return Boolean
      with Subprogram_Variant => (Decreases => Length (S)), Pre => X <= M'Last;

      --  Local Lemmas

      procedure Lemma_Reachable_Inc
        (X : Positive_Count_Type; M : Memory_Type; S1, S2 : Memory_Index_Set)
      with
        Subprogram_Variant => (Decreases => Length (S1)),
        Pre                => X <= M'Last and then S1 <= S2,
        Post               =>
          Reachable_Set_Internal (X, M, S1)
          <= Reachable_Set_Internal (X, M, S2);

      procedure Lemma_Reachable_Cut
        (X, Y : Positive_Count_Type; M : Memory_Type; S : Memory_Index_Set)
      with
        Subprogram_Variant => (Decreases => Length (S)),
        Pre                =>
          X <= M'Last and then Y <= M'Last and then Contains (S, Y),
        Post               =>
          Included_In_Union
            (Reachable_Set_Internal (X, M, S),
             Reachable_Set_Internal (X, M, Remove (S, Y)),
             Reachable_Set_Internal (Y, M, S));

      procedure Lemma_Reachable_Ext
        (X : Positive_Count_Type; M : Memory_Type; S1, S2 : Memory_Index_Set)
      with
        Ghost,
        Subprogram_Variant => (Decreases => Length (S1)),
        Pre                =>
          X <= M'Last
          and then Well_Formed_Internal (X, M, S1)
          and then S1 <= S2,
        Post               =>
          Reachable_Set_Internal (X, M, S1) = Reachable_Set_Internal (X, M, S2);

      procedure Lemma_Reachable_Preserved
        (X : Count_Type; M1, M2 : Memory_Type; S : Memory_Index_Set)
      with
        Ghost,
        Subprogram_Variant => (Decreases => Length (S)),
        Pre                =>
          M1'Last = M2'Last
          and then X <= M1'Last
          and then (for all I of Reachable_Set_Internal (X, M1, S) =>
                      M1 (I).Next = M2 (I).Next),
        Post               =>
          Reachable_Set_Internal (X, M1, S) = Reachable_Set_Internal (X, M2, S);

      procedure Lemma_Reachable_Antisym
        (X, Y : Positive_Count_Type; M : Memory_Type)
      with
        Pre  => X <= M'Last and then Y <= M'Last and then Well_Formed (X, M),
        Post => (if Reachable (X, M, Y) and Reachable (Y, M, X) then X = Y);

      procedure Lemma_Reachable_Well_Formed
        (X, Y : Positive_Count_Type; M : Memory_Type)
      with
        Pre  =>
          X <= M'Last
          and then Y <= M'Last
          and then Well_Formed (X, M)
          and then Reachable (X, M, Y),
        Post => Well_Formed (Y, M);

      procedure Lemma_Well_Formed_Inc
        (X : Positive_Count_Type; M : Memory_Type; S1, S2 : Memory_Index_Set)
      with
        Subprogram_Variant => (Decreases => Length (S1)),
        Pre                => X <= M'Last and then S1 <= S2,
        Post               =>
          (if Well_Formed_Internal (X, M, S1)
           then Well_Formed_Internal (X, M, S2));

      procedure Lemma_Well_Formed_Preserved
        (X : Count_Type; M1, M2 : Memory_Type; S : Memory_Index_Set)
      with
        Ghost,
        Subprogram_Variant => (Decreases => Length (S)),
        Pre                =>
          M1'Last = M2'Last
          and then X <= M1'Last
          and then (for all I of Reachable_Set_Internal (X, M1, S) =>
                      M1 (I).Next = M2 (I).Next),
        Post               =>
          Well_Formed_Internal (X, M1, S) = Well_Formed_Internal (X, M2, S);

      procedure Lemma_Well_Formed_Cut
        (X, Y : Positive_Count_Type; M : Memory_Type; S : Memory_Index_Set)
      with
        Ghost,
        Subprogram_Variant => (Decreases => Length (S)),
        Pre                =>
          X <= M'Last and then Y <= M'Last and then Contains (S, Y),
        Post               =>
          (if Well_Formed_Internal (X, M, S)
           then
             Well_Formed_Internal (X, M, Remove (S, Y))
             or (Contains (Reachable_Set_Internal (X, M, S), Y)
                 and Well_Formed_Internal (Y, M, S)));

      --  Subprogram bodies

      function All_From_Seq (Fst, Lst : Count_Type) return Sequence is
      begin
         return S : Sequence do
            if Fst < Lst then
               for I in reverse Fst + 1 .. Lst loop
                  S := Add (S, I);
                  pragma Loop_Invariant (Length (S) = To_Big (Lst - I + 1));
                  pragma
                    Loop_Invariant
                      (for all K in Interval'(1, To_Big (Lst - I + 1)) =>
                         To_Big (Get (S, K)) = To_Big (Lst) - K + 1);
               end loop;
            end if;
         end return;
      end All_From_Seq;

      function All_Set (Capacity : Count_Type) return Memory_Index_Set is
      begin
         return S : Memory_Index_Set do
            for I in 1 .. Capacity loop
               S := Add (S, I);
               pragma Loop_Invariant (Length (S) = To_Big (I));
               pragma Loop_Invariant (for all K in 1 .. I => Contains (S, K));
               pragma Loop_Invariant (for all K of S => K in 1 .. I);
            end loop;
         end return;
      end All_Set;

      function Empty_Seq return Sequence is
      begin
         return S : Sequence do
            null;
         end return;
      end Empty_Seq;

      function Empty_Set return Memory_Index_Set is
      begin
         return S : Memory_Index_Set do
            null;
         end return;
      end Empty_Set;

      function Find
        (M : Memory_Type; Fst : Count_Type; I : Positive_Count_Type)
         return Big_Natural
      is
         pragma
           Annotate
             (GNATprove, Unhide_Info, "Expression_Function_Body", LL_Sequence);
         C : Count_Type range 0 .. M'Last := Fst;
      begin
         while C /= 0 loop
            pragma Loop_Invariant (Well_Formed (C, M));
            pragma Loop_Invariant (LL_Sequence (C, M) <= LL_Sequence (Fst, M));
            pragma Loop_Invariant (Reachable (C, M, I) = Reachable (Fst, M, I));
            pragma
              Loop_Invariant
                (for all K in
                   Interval'
                     (Last (LL_Sequence (C, M)) + 1,
                      Last (LL_Sequence (Fst, M))) =>
                   Get (LL_Sequence (Fst, M), K) /= I);
            pragma Loop_Variant (Decreases => Length (Reachable_Set (C, M)));
            if C = I then
               return Last (LL_Sequence (I, M));
            end if;
            Lemma_Well_Formed_Def (C, M);
            Lemma_Reachable_Def (C, M);
            C := M (C).Next;
         end loop;
         return 0;
      end Find;

      function Find
        (M : Memory_Type; Fst : Count_Type; E : Element_Type) return Big_Natural
      is
         pragma
           Annotate
             (GNATprove, Unhide_Info, "Expression_Function_Body", LL_Sequence);
         C : Count_Type range 0 .. M'Last := Fst;
      begin
         while C /= 0 loop
            pragma Loop_Invariant (Well_Formed (C, M));
            pragma Loop_Invariant (LL_Sequence (C, M) <= LL_Sequence (Fst, M));
            pragma
              Loop_Invariant (Reachable_Set (C, M) <= Reachable_Set (Fst, M));
            pragma
              Loop_Invariant
                (for all K in
                   Interval'
                     (Last (LL_Sequence (C, M)) + 1,
                      Last (LL_Sequence (Fst, M))) =>
                   not Equivalent_Elements
                         (M (Get (LL_Sequence (Fst, M), K)).Value.V, E));
            pragma Loop_Variant (Decreases => Length (Reachable_Set (C, M)));
            if Equivalent_Elements (M (C).Value.V, E) then
               return Last (LL_Sequence (C, M));
            end if;
            Lemma_Well_Formed_Def (C, M);
            Lemma_Reachable_Def (C, M);
            C := M (C).Next;
         end loop;
         return 0;
      end Find;

      function LL_Sequence_Internal
        (X : Count_Type; M : Memory_Type) return Sequence is
      begin
         if X = 0 then
            return Empty_Seq;
         else
            Lemma_Well_Formed_Def (X, M);
            Lemma_Reachable_Def (X, M);

            return Add (LL_Sequence_Internal (M (X).Next, M), X);
         end if;
      end LL_Sequence_Internal;

      function LL_Sequence (X : Count_Type; M : Memory_Type) return Sequence
      is (LL_Sequence_Internal (X, M));

      function Reachable_Set_Internal
        (X : Count_Type; M : Memory_Type; S : Memory_Index_Set)
         return Memory_Index_Set
      is (if X = 0 or else not Contains (S, X)
          then Empty_Set
          else Add (Reachable_Set_Internal (M (X).Next, M, Remove (S, X)), X));

      function Reachable_Set
        (X : Count_Type; M : Memory_Type) return Memory_Index_Set
      is (Reachable_Set_Internal (X, M, All_Set (M'Last)));

      function Values_From_Memory (S : Set) return Values_Type is
         pragma
           Annotate
             (GNATprove,
              Unhide_Info,
              "Expression_Function_Body",
              Values_From_Memory_Buckets);
         C : Count_Type range 0 .. S.Capacity;
      begin
         return M : Values_Type do
            for B in 1 .. S.Modulus loop
               C := S.Buckets (B);
               while C > 0 loop
                  pragma Loop_Invariant (Well_Formed (C, S.Memory));
                  pragma
                    Loop_Invariant
                      (Reachable_Set (C, S.Memory)
                         <= Reachable_Set (S.Buckets (B), S.Memory));
                  pragma
                    Loop_Invariant
                      (for all I of M =>
                         Find_Bucket (Get (M, I), S.Modulus) <= B);
                  pragma
                    Loop_Invariant
                      (for all I of M => not Reachable (C, S.Memory, I));
                  pragma
                    Loop_Invariant
                      (for all I of M =>
                         Reachable
                           (S.Buckets (Find_Bucket (Get (M, I), S.Modulus)),
                            S.Memory,
                            I));
                  pragma
                    Loop_Invariant
                      (for all B2 in S.Buckets'First .. B - 1 =>
                         (for all I of
                            Reachable_Set (S.Buckets (B2), S.Memory) =>
                            Has_Key (M, I)));
                  pragma
                    Loop_Invariant
                      (for all I of Reachable_Set (S.Buckets (B), S.Memory) =>
                         Reachable (C, S.Memory, I) or Has_Key (M, I));
                  pragma
                    Loop_Invariant
                      (for all I of M =>
                         S.Memory (I).Value'Initialized
                         and then S.Memory (I).Value.V = Get (M, I));
                  pragma
                    Loop_Variant
                      (Decreases => Length (Reachable_Set (C, S.Memory)));
                  M := Add (M, C, S.Memory (C).Value.V);
                  Lemma_Well_Formed_Def (C, S.Memory);
                  Lemma_Reachable_Def (C, S.Memory);
                  C := S.Memory (C).Next;
               end loop;
               pragma
                 Assert
                   (for all I of Reachable_Set (S.Buckets (B), S.Memory) =>
                      Has_Key (M, I));
               pragma
                 Loop_Invariant
                   (for all I of M => Find_Bucket (Get (M, I), S.Modulus) <= B);
               pragma
                 Loop_Invariant
                   (for all I of M =>
                      Reachable
                        (S.Buckets (Find_Bucket (Get (M, I), S.Modulus)),
                         S.Memory,
                         I));
               pragma
                 Loop_Invariant
                   (for all B2 in 1 .. B =>
                      (for all I of Reachable_Set (S.Buckets (B2), S.Memory) =>
                         Has_Key (M, I)));
               pragma
                 Loop_Invariant
                   (for all I of M =>
                      S.Memory (I).Value'Initialized
                      and then S.Memory (I).Value.V = Get (M, I));
            end loop;
         end return;
      end Values_From_Memory;

      function Well_Formed_Internal
        (X : Count_Type; M : Memory_Type; S : Memory_Index_Set) return Boolean
      is (if X = 0
          then True
          elsif not Contains (S, X)
          then False
          else Well_Formed_Internal (M (X).Next, M, Remove (S, X)));

      function Well_Formed (X : Count_Type; M : Memory_Type) return Boolean
      is (Well_Formed_Internal (X, M, All_Set (M'Last)));

      --  Proofs of lemmas

      procedure Lemma_Reachable_Inc
        (X : Positive_Count_Type; M : Memory_Type; S1, S2 : Memory_Index_Set) is
      begin
         if Contains (S1, X) and then M (X).Next /= 0 then
            Lemma_Reachable_Inc (M (X).Next, M, Remove (S1, X), Remove (S2, X));
         end if;
      end Lemma_Reachable_Inc;

      procedure Lemma_Reachable_Cut
        (X, Y : Positive_Count_Type; M : Memory_Type; S : Memory_Index_Set) is
      begin
         if M (X).Next /= 0 and X /= Y and Contains (S, X) then
            Lemma_Reachable_Cut (M (X).Next, Y, M, Remove (S, X));
            Lemma_Reachable_Inc
              (M (X).Next,
               M,
               Remove (Remove (S, X), Y),
               Remove (Remove (S, Y), X));
            Lemma_Reachable_Inc
              (M (X).Next,
               M,
               Remove (Remove (S, Y), X),
               Remove (Remove (S, X), Y));
            Lemma_Reachable_Inc (Y, M, Remove (S, X), S);
         end if;
      end Lemma_Reachable_Cut;

      procedure Lemma_Well_Formed_Inc
        (X : Positive_Count_Type; M : Memory_Type; S1, S2 : Memory_Index_Set) is
      begin
         if Contains (S1, X) and then M (X).Next /= 0 then
            Lemma_Well_Formed_Inc
              (M (X).Next, M, Remove (S1, X), Remove (S2, X));
         end if;
      end Lemma_Well_Formed_Inc;

      procedure Lemma_Well_Formed_Preserved
        (X : Count_Type; M1, M2 : Memory_Type; S : Memory_Index_Set) is
      begin
         if X > 0 and then Contains (S, X) then
            Lemma_Well_Formed_Preserved (M1 (X).Next, M1, M2, Remove (S, X));
         end if;
      end Lemma_Well_Formed_Preserved;

      procedure Lemma_Well_Formed_Preserved
        (X : Count_Type; M1, M2 : Memory_Type)
      is
         pragma
           Annotate
             (GNATprove, Unhide_Info, "Expression_Function_Body", Well_Formed);
         pragma
           Annotate
             (GNATprove,
              Unhide_Info,
              "Expression_Function_Body",
              Reachable_Set);
      begin
         Lemma_Well_Formed_Preserved (X, M1, M2, All_Set (M1'Last));
      end Lemma_Well_Formed_Preserved;

      procedure Lemma_Values_Buckets
        (S : Set; B : Positive_Hash_Type; I : Positive_Count_Type)
      is null;
      pragma
        Annotate
          (GNATprove,
           Unhide_Info,
           "Expression_Function_Body",
           Values_From_Memory_Buckets);

      procedure Lemma_Values_Preserved (S1, S2 : Set; I : Count_Type := 0)
      is null;
      pragma
        Annotate
          (GNATprove,
           Unhide_Info,
           "Expression_Function_Body",
           Values_From_Memory_Buckets);

      procedure Lemma_Well_Formed_Cut
        (X, Y : Positive_Count_Type; M : Memory_Type; S : Memory_Index_Set) is
      begin
         if M (X).Next /= 0 and X /= Y and Contains (S, X) then
            Lemma_Well_Formed_Cut (M (X).Next, Y, M, Remove (S, X));
            Lemma_Well_Formed_Inc
              (M (X).Next,
               M,
               Remove (Remove (S, X), Y),
               Remove (Remove (S, Y), X));
            Lemma_Well_Formed_Inc
              (M (X).Next,
               M,
               Remove (Remove (S, Y), X),
               Remove (Remove (S, X), Y));
            Lemma_Well_Formed_Inc (Y, M, Remove (S, X), S);
         end if;
      end Lemma_Well_Formed_Cut;

      procedure Lemma_Well_Formed_Set
        (X, Y : Positive_Count_Type; Z : Count_Type; M1, M2 : Memory_Type) is
      begin
         Lemma_Well_Formed_Def (X, M2);
         if X = Y then
            Lemma_Well_Formed_Preserved (Z, M1, M2);
         else
            Lemma_Well_Formed_Def (X, M1);
            Lemma_Reachable_Def (X, M1);
            Lemma_Well_Formed_Set (M1 (X).Next, Y, Z, M1, M2);
         end if;
      end Lemma_Well_Formed_Set;

      procedure Lemma_Well_Formed_Def (X : Positive_Count_Type; M : Memory_Type)
      is
         pragma
           Annotate
             (GNATprove, Unhide_Info, "Expression_Function_Body", Well_Formed);
      begin
         if Well_Formed (X, M) and M (X).Next /= 0 then
            Lemma_Well_Formed_Inc
              (M (X).Next, M, Remove (All_Set (M'Last), X), All_Set (M'Last));
         end if;
         if Well_Formed (M (X).Next, M) and M (X).Next /= 0 then
            Lemma_Well_Formed_Cut (M (X).Next, X, M, All_Set (M'Last));
         end if;
      end Lemma_Well_Formed_Def;

      procedure Lemma_Reachable_Ext
        (X : Positive_Count_Type; M : Memory_Type; S1, S2 : Memory_Index_Set) is
      begin
         if M (X).Next /= 0 then
            Lemma_Reachable_Ext (M (X).Next, M, Remove (S1, X), Remove (S2, X));
         end if;
      end Lemma_Reachable_Ext;

      procedure Lemma_Reachable_Def (X : Positive_Count_Type; M : Memory_Type)
      is
         pragma
           Annotate
             (GNATprove, Unhide_Info, "Expression_Function_Body", Well_Formed);
         pragma
           Annotate
             (GNATprove,
              Unhide_Info,
              "Expression_Function_Body",
              Reachable_Set);

         procedure Lemma_Reachable_Def
           (X : Positive_Count_Type; M : Memory_Type; S : Memory_Index_Set)
         with
           Subprogram_Variant => (Decreases => Length (S)),
           Pre                => X <= M'Last and then Contains (S, X),
           Post               =>
             Reachable_Set_Internal (X, M, S)
             = (if Contains
                     (Reachable_Set_Internal (M (X).Next, M, Remove (S, X)), X)
                then Reachable_Set_Internal (M (X).Next, M, Remove (S, X))
                else
                  Add
                    (Reachable_Set_Internal (M (X).Next, M, Remove (S, X)), X))
         is
         begin
            if M (X).Next /= 0 and then Contains (Remove (S, X), M (X).Next)
            then
               Lemma_Reachable_Def (M (X).Next, M, Remove (S, X));
            end if;
         end Lemma_Reachable_Def;
      begin
         Lemma_Reachable_Def (X, M, All_Set (M'Last));
         if M (X).Next /= 0 then
            Lemma_Reachable_Inc
              (M (X).Next, M, Remove (All_Set (M'Last), X), All_Set (M'Last));
            Lemma_Reachable_Cut (M (X).Next, X, M, All_Set (M'Last));
         end if;
         pragma
           Assert
             (Reachable_Set (X, M)
                = (if Contains (Reachable_Set (M (X).Next, M), X)
                   then Reachable_Set (M (X).Next, M)
                   else Add (Reachable_Set (M (X).Next, M), X)));
         if M (X).Next /= 0 then
            Lemma_Reachable_Ext
              (M (X).Next, M, Remove (All_Set (M'Last), X), All_Set (M'Last));
            --  Call Num_Overlap to get the equality of lengths on = sets
            pragma
              Assert
                (Num_Overlaps
                   (Reachable_Set (X, M),
                    Add
                      (Reachable_Set_Internal (M (X).Next, M, All_Set (M'Last)),
                       X))
                   = Length (Reachable_Set (X, M)));
         end if;
      end Lemma_Reachable_Def;

      procedure Lemma_Reachable_Preserved
        (X : Count_Type; M1, M2 : Memory_Type; S : Memory_Index_Set) is
      begin
         if X > 0 and then Contains (S, X) then
            Lemma_Reachable_Preserved (M1 (X).Next, M1, M2, Remove (S, X));
         end if;
      end Lemma_Reachable_Preserved;

      procedure Lemma_Reachable_Preserved (X : Count_Type; M1, M2 : Memory_Type)
      is
         pragma
           Annotate
             (GNATprove,
              Unhide_Info,
              "Expression_Function_Body",
              Reachable_Set);
      begin
         Lemma_Reachable_Preserved (X, M1, M2, All_Set (M1'Last));
         --  Call Num_Overlap to get the equality of lengths on = sets
         pragma
           Assert
             (Num_Overlaps (Reachable_Set (X, M1), Reachable_Set (X, M2))
                = Length (Reachable_Set (X, M1)));
      end Lemma_Reachable_Preserved;

      procedure Lemma_Reachable_Antisym
        (X, Y : Positive_Count_Type; M : Memory_Type)
      is
         pragma
           Annotate
             (GNATprove, Unhide_Info, "Expression_Function_Body", Well_Formed);
         pragma
           Annotate
             (GNATprove,
              Unhide_Info,
              "Expression_Function_Body",
              Reachable_Set);

         C : Count_Type range 0 .. M'Last := M (X).Next;
      begin
         if X /= Y and Reachable (X, M, Y) then

            --  X is not accessible from M (X).Next

            Lemma_Reachable_Ext
              (M (X).Next, M, Remove (All_Set (M'Last), X), All_Set (M'Last));
            Lemma_Well_Formed_Def (X, M);

            --  Go over the element accessible from X to prove that X is not
            --  accessible from them.

            loop
               pragma Loop_Invariant (Well_Formed (C, M));
               pragma Loop_Invariant (Reachable (C, M, Y));
               pragma Loop_Invariant (not Reachable (C, M, X));
               pragma Loop_Variant (Decreases => Length (Reachable_Set (C, M)));
               exit when C = Y;
               Lemma_Well_Formed_Def (C, M);
               Lemma_Reachable_Def (C, M);
               C := M (C).Next;
            end loop;
         end if;
      end Lemma_Reachable_Antisym;

      procedure Lemma_Reachable_Well_Formed
        (X, Y : Positive_Count_Type; M : Memory_Type)
      is
         C : Positive_Count_Type range M'Range := X;
      begin
         --  Go over the element accessible from X to prove that they are well
         --  formed.

         loop
            pragma Loop_Invariant (Well_Formed (C, M));
            pragma Loop_Invariant (Reachable (C, M, Y));
            pragma Loop_Variant (Decreases => Length (Reachable_Set (C, M)));
            exit when C = Y;
            Lemma_Well_Formed_Def (C, M);
            Lemma_Reachable_Def (C, M);
            C := M (C).Next;
         end loop;
      end Lemma_Reachable_Well_Formed;

      procedure Lemma_Reachable_Set
        (X, Y : Positive_Count_Type; Z : Count_Type; M1, M2 : Memory_Type) is
      begin
         Lemma_Well_Formed_Set (X, Y, Z, M1, M2);
         Lemma_Reachable_Def (X, M2);
         Lemma_Well_Formed_Def (X, M1);
         Lemma_Reachable_Def (X, M1);
         if X = Y then
            Lemma_Reachable_Preserved (Z, M1, M2);
         else
            Lemma_Reachable_Antisym (X, Y, M1);
            Lemma_Reachable_Well_Formed (X, Y, M1);
            Lemma_Reachable_Def (Y, M1);
            Lemma_Reachable_Set (M1 (X).Next, Y, Z, M1, M2);
         end if;
      end Lemma_Reachable_Set;

      procedure Lemma_Length_Complete (S : Set) is
         Free_Cells      : Memory_Index_Set;
         Allocated_Cells : Memory_Index_Set;

      begin
         --  Construct the set of free cells

         if S.Free >= 0 then
            Free_Cells := Reachable_Set (S.Free, S.Memory);
         else
            for I in -S.Free .. S.Capacity loop
               Free_Cells := Add (Free_Cells, I);
               pragma
                 Loop_Invariant (Length (Free_Cells) = To_Big (I + S.Free + 1));
               pragma
                 Loop_Invariant
                   (for all K in -S.Free .. I => Contains (Free_Cells, K));
               pragma
                 Loop_Invariant (for all K of Free_Cells => K in -S.Free .. I);
            end loop;
         end if;
         pragma
           Assert
             (for all I in S.Memory'Range =>
                Is_Free (S.Free, S.Memory, I) = Contains (Free_Cells, I));

         --  Construct the set of allocated cells

         for B in S.Buckets'Range loop
            pragma
              Assert
                (No_Overlap
                   (Allocated_Cells, Reachable_Set (S.Buckets (B), S.Memory)));
            Allocated_Cells :=
              Union (Allocated_Cells, Reachable_Set (S.Buckets (B), S.Memory));
            pragma
              Loop_Invariant
                (for all I of Allocated_Cells =>
                   (for some K in 1 .. B =>
                      Contains (Reachable_Set (S.Buckets (K), S.Memory), I)));
            pragma
              Loop_Invariant
                (for all K in 1 .. B =>
                   Reachable_Set (S.Buckets (K), S.Memory) <= Allocated_Cells);
            pragma
              Loop_Invariant
                (Length (Allocated_Cells)
                   = Num_Allocated (S.Buckets, S.Memory, B));
            pragma
              Loop_Invariant
                (Is_Empty (Intersection (Allocated_Cells, Free_Cells)));
         end loop;
         pragma
           Assert
             (for all I in S.Memory'Range =>
                Is_Allocated (S.Buckets, S.Memory, I)
                = Contains (Allocated_Cells, I));

         pragma Assert (Num_Overlaps (Allocated_Cells, Free_Cells) = 0);
         pragma
           Assert
             (Num_Overlaps
                (Union (Allocated_Cells, Free_Cells), All_Set (S.Capacity))
                = To_Big (S.Capacity));
      end Lemma_Length_Complete;

      procedure Lemma_LL_Sequence_Def (X : Count_Type; M : Memory_Type) is
         pragma
           Annotate
             (GNATprove, Unhide_Info, "Expression_Function_Body", LL_Sequence);
      begin
         if X /= 0 then
            Lemma_Well_Formed_Def (X, M);
         end if;
      end Lemma_LL_Sequence_Def;

      procedure Lemma_LL_Sequence_Preserved
        (X : Count_Type; M1, M2 : Memory_Type) is
      begin
         Lemma_Well_Formed_Preserved (X, M1, M2);
         if X /= 0 then
            Lemma_Well_Formed_Def (X, M1);
            Lemma_Reachable_Def (X, M1);
            Lemma_LL_Sequence_Preserved (M1 (X).Next, M1, M2);
            Lemma_LL_Sequence_Def (X, M1);
            Lemma_LL_Sequence_Def (X, M2);
         end if;
      end Lemma_LL_Sequence_Preserved;

      procedure Lemma_LL_Sequence_Set
        (X, Y : Positive_Count_Type; Z : Count_Type; M1, M2 : Memory_Type)
      is
         pragma
           Annotate
             (GNATprove, Unhide_Info, "Expression_Function_Body", LL_Sequence);
      begin
         Lemma_Well_Formed_Set (X, Y, Z, M1, M2);
         Lemma_Well_Formed_Def (X, M1);
         Lemma_Reachable_Def (X, M1);
         if X = Y then
            Lemma_LL_Sequence_Preserved (Z, M1, M2);
         else
            Lemma_Reachable_Well_Formed (X, Y, M1);
            Lemma_LL_Sequence_Set (M1 (X).Next, Y, Z, M1, M2);
            Lemma_Well_Formed_Def (X, M2);
            pragma
              Assert
                (for all I in
                   Interval'
                     (Last (LL_Sequence (Y, M1)) + 1,
                      Last (LL_Sequence (X, M1))) =>
                   Get (LL_Sequence (X, M1), I)
                   = Get
                       (LL_Sequence (X, M2),
                        I
                        - Last (LL_Sequence (Y, M1))
                        + Last (LL_Sequence (Z, M1))
                        + 1));
            pragma
              Assert
                (for all I in
                   Interval'
                     (Last (LL_Sequence (Z, M1)) + 1,
                      Last (LL_Sequence (X, M2))) =>
                   Get (LL_Sequence (X, M2), I)
                   = Get
                       (LL_Sequence (X, M1),
                        I
                        - Last (LL_Sequence (Z, M1))
                        + Last (LL_Sequence (Y, M1))
                        - 1));
         end if;
      end Lemma_LL_Sequence_Set;

      procedure Lemma_LL_Sequence_No_Duplicated_Indexes (S : Set; B : Hash_Type)
      is
         pragma
           Annotate
             (GNATprove,
              Hide_Info,
              "Expression_Function_Body",
              LL_Correct_Free_List);

         C : Count_Type range 0 .. S.Capacity := S.Buckets (B);
      begin
         while C /= 0 loop
            Lemma_Well_Formed_Def (C, S.Memory);
            Lemma_Reachable_Def (C, S.Memory);
            Lemma_LL_Sequence_Def (C, S.Memory);
            C := S.Memory (C).Next;

            pragma
              Loop_Variant (Decreases => Length (Reachable_Set (C, S.Memory)));
            pragma Loop_Invariant (Well_Formed (C, S.Memory));
            pragma
              Loop_Invariant
                (LL_Sequence (C, S.Memory)
                   <= LL_Sequence (S.Buckets (B), S.Memory));
            pragma
              Loop_Invariant
                (for all P1 in
                   Interval'
                     (Length (LL_Sequence (C, S.Memory)) + 1,
                      Length (LL_Sequence (S.Buckets (B), S.Memory))) =>
                   (for all P2 in Interval'(1, P1 - 1) =>
                      Get (LL_Sequence (S.Buckets (B), S.Memory), P1)
                      /= Get (LL_Sequence (S.Buckets (B), S.Memory), P2)));
         end loop;
      end Lemma_LL_Sequence_No_Duplicated_Indexes;

   end Private_Model;

   use Private_Model.Memory_Index_Sets;

   pragma Unevaluated_Use_Of_Old (Allow);

   type Primes_Type is array (Positive range <>) of Positive_Hash_Type;

   Primes : constant Primes_Type :=
     [53,
      97,
      193,
      389,
      769,
      1543,
      3079,
      6151,
      12289,
      24593,
      49157,
      98317,
      196613,
      393241,
      786433,
      1572869,
      3145739,
      6291469,
      12582917,
      25165843,
      50331653,
      100663319,
      201326611,
      402653189,
      805306457,
      1610612741,
      3221225473,
      4294967291];

   function To_Prime (Length : Count_Type) return Positive_Hash_Type;
   --  Returns the smallest value in Primes not less than Length

   procedure Allocate (S : in out Set; I : out Positive_Count_Type)
   with
     Pre  => LL_Invariant (S) and then Num_Allocated (S) < To_Big (S.Capacity),
     Post =>
       I = Get (LL_Free (S)'Old, Last (LL_Free (S))'Old)
       and then I <= S.Capacity
       and then LL_Correct (S)
       and then LL_Length (S)
       and then LL_Has_Element (S)
       and then (for all K in 1 .. S.Capacity =>
                   (if K /= I
                    then
                      Is_Free (S.Free, S.Memory, K)
                      or else Is_Allocated (S.Buckets, S.Memory, K)))
       and then S.Length = S.Length'Old
       and then not Is_Free (S.Free, S.Memory, I)
       and then (for all B of S.Buckets => not Reachable (B, S.Memory, I))
       and then LL_Model (S).Values = LL_Model (S).Values'Old
       and then LL_Model (S).Buckets = LL_Model (S).Buckets'Old
       and then Is_Remove
                  (LL_Free (S)'Old, Last (LL_Free (S)'Old), LL_Free (S));

   procedure Deallocate (S : in out Set; I : Positive_Count_Type)
   with
     Pre  =>
       LL_Correct (S)
       and then LL_Length (S)
       and then LL_Has_Element (S)
       and then I <= S.Capacity
       and then (for all K in 1 .. S.Capacity =>
                   (if K /= I
                    then
                      Is_Free (S.Free, S.Memory, K)
                      or else Is_Allocated (S.Buckets, S.Memory, K)))
       and then not Is_Free (S.Free, S.Memory, I)
       and then (for all B of S.Buckets => not Reachable (B, S.Memory, I)),
     Post =>
       LL_Invariant (S)
       and then S.Length = S.Length'Old
       and then LL_Model (S).Values'Old = LL_Model (S).Values
       and then LL_Model (S).Buckets = LL_Model (S).Buckets'Old
       and then Is_Add (LL_Free (S)'Old, I, LL_Free (S));

   procedure Insert_Internal
     (S : in out Set; I : Positive_Count_Type; E : Element_Type)
   with
     Pre  =>
       LL_Correct (S)
       and then LL_Length (S)
       and then LL_Has_Element (S)
       and then S.Length < S.Capacity
       and then I <= S.Capacity
       and then (for all K in 1 .. S.Capacity =>
                   (if K /= I
                    then
                      Is_Free (S.Free, S.Memory, K)
                      or else Is_Allocated (S.Buckets, S.Memory, K)))
       and then not Is_Free (S.Free, S.Memory, I)
       and then (for all K of S.Buckets => not Reachable (K, S.Memory, I)),
     Post =>
       LL_Correct (S)
       and then LL_Length (S)
       and then LL_Complete (S)
       and then LL_Has_Element (S)
       and then S.Length = S.Length'Old + 1
       and then LL_Free (S) = LL_Free (S)'Old
       and then Is_Add
                  (LL_Model (S).Buckets (Find_Bucket (E, S.Modulus))'Old,
                   I,
                   LL_Model (S).Buckets (Find_Bucket (E, S.Modulus)))
       and then (for all K in 1 .. S.Modulus =>
                   (if Find_Bucket (E, S.Modulus) /= K
                    then
                      LL_Model (S).Buckets (K) = LL_Model (S).Buckets'Old (K)))
       and then LL_Model (S).Values'Old <= LL_Model (S).Values
       and then Keys_Included_Except
                  (LL_Model (S).Values, LL_Model (S).Values'Old, I)
       and then Get (LL_Model (S).Values, I) = E;

   procedure Delete_No_Free (S : in out Set; I : Positive_Count_Type)
   with
     Pre  =>
       LL_Correct (S)
       and then LL_Complete (S)
       and then LL_Length (S)
       and then LL_Has_Element (S)
       and then Has_Element (S, I),
     Post =>
       LL_Correct (S)
       and then LL_Length (S)
       and then LL_Has_Element (S)
       and then (for all K in 1 .. S.Capacity =>
                   (if K /= I
                    then
                      Is_Free (S.Free, S.Memory, K)
                      or else Is_Allocated (S.Buckets, S.Memory, K)))
       and then not Is_Free (S.Free, S.Memory, I)
       and then (for all B of S.Buckets => not Reachable (B, S.Memory, I))
       and then S.Length = S.Length'Old - 1
       and then LL_Free (S) = LL_Free (S)'Old
       and then Is_Remove
                  (LL_Model (S).Buckets
                     (Find_Bucket (S.Memory (I).Value.V, S.Modulus))'Old,
                   Formal_Model.Find
                     (LL_Model (S).Buckets
                        (Find_Bucket (S.Memory (I).Value.V, S.Modulus)),
                      I)'Old,
                   LL_Model (S).Buckets
                     (Find_Bucket (S.Memory (I).Value.V, S.Modulus)'Old))
       and then (for all K in 1 .. S.Modulus =>
                   (if Find_Bucket (S.Memory (I).Value.V, S.Modulus) /= K
                    then
                      LL_Model (S).Buckets (K) = LL_Model (S).Buckets'Old (K)))
       and then LL_Model (S).Values <= LL_Model (S).Values'Old
       and then Keys_Included_Except
                  (LL_Model (S).Values'Old, LL_Model (S).Values, I);

   procedure Delete_Key_No_Free
     (S : in out Set; E : Element_Type; I : out Count_Type)
   with
     Pre  =>
       LL_Correct (S)
       and then LL_Complete (S)
       and then LL_Length (S)
       and then LL_Has_Element (S),
     Post =>
       (if Formal_Model.Find
             (LL_Model (S).Buckets (Find_Bucket (E, S.Modulus)),
              LL_Model (S).Values,
              E)'Old
          = 0
        then
          I = 0
          and then LL_Correct (S)
          and then LL_Complete (S)
          and then LL_Length (S)
          and then LL_Has_Element (S)
          and then LL_Model (S) = LL_Model (S)'Old
        else
          LL_Correct (S)
          and then LL_Length (S)
          and then LL_Has_Element (S)
          and then I
                   = Get
                       (LL_Model (S).Buckets (Find_Bucket (E, S.Modulus))'Old,
                        Formal_Model.Find
                          (LL_Model (S).Buckets (Find_Bucket (E, S.Modulus)),
                           LL_Model (S).Values,
                           E)'Old)
          and then I <= S.Capacity
          and then (for all K in 1 .. S.Capacity =>
                      (if K /= I
                       then
                         Is_Free (S.Free, S.Memory, K)
                         or else Is_Allocated (S.Buckets, S.Memory, K)))
          and then not Is_Free (S.Free, S.Memory, I)
          and then (for all B of S.Buckets => not Reachable (B, S.Memory, I))
          and then Is_Remove
                     (LL_Model (S).Buckets (Find_Bucket (E, S.Modulus))'Old,
                      Find
                        (LL_Model (S).Buckets (Find_Bucket (E, S.Modulus)),
                         LL_Model (S).Values,
                         E)'Old,
                      LL_Model (S).Buckets (Find_Bucket (E, S.Modulus)))
          and then S.Length = S.Length'Old - 1
          and then LL_Free (S) = LL_Free (S)'Old
          and then (for all K in 1 .. S.Modulus =>
                      (if Find_Bucket (E, S.Modulus) /= K
                       then
                         LL_Model (S).Buckets (K)
                         = LL_Model (S).Buckets'Old (K)))
          and then LL_Model (S).Values <= LL_Model (S).Values'Old
          and then Keys_Included_Except
                     (LL_Model (S).Values'Old, LL_Model (S).Values, I));

   --------------
   -- To_Prime --
   --------------

   function To_Prime (Length : Count_Type) return Positive_Hash_Type is
      I, J, K : Integer'Base;
      Index   : Integer'Base;

   begin
      I := Primes'Last - Primes'First;
      Index := Primes'First;
      while I > 0 loop
         pragma Loop_Invariant (Index in Primes'Range);
         pragma Loop_Invariant (I <= Primes'Last - Index);
         pragma Loop_Variant (Decreases => I);
         J := I / 2;
         K := Index + J;

         if Primes (K) < Hash_Type (Length) then
            Index := K + 1;
            I := I - J - 1;
         else
            I := J;
         end if;
      end loop;

      return Primes (Index);
   end To_Prime;

   function Length (S : Set) return Count_Type
   with
     Refined_Post =>
       To_Big (Length'Result) = Num_Allocated (LL_Model (S).Buckets)
       and Length'Result = S.Length
   is
      M : constant Set_LL_Model := LL_Model (S)
      with Ghost;
      procedure Prove_Post with Ghost is
      begin
         for B in 1 .. S.Modulus loop
            pragma
              Loop_Invariant
                (Num_Allocated (M.Buckets, B)
                   = Num_Allocated (S.Buckets, S.Memory, B));
         end loop;
      end Prove_Post;
   begin
      Prove_Post;
      return S.Length;
   end Length;

   function Default_Modulus (C : Count_Type) return Positive_Hash_Type;

   function Default_Modulus (C : Count_Type) return Positive_Hash_Type is
   begin
      return To_Prime (C);
   end Default_Modulus;

   function Empty_Set (Capacity : Count_Type) return Set is
      Modulus : constant Positive_Hash_Type := Default_Modulus (Capacity);
      V       : Relaxed_Element;
   begin
      return
         S : Set :=
           (Capacity => Capacity,
            Modulus  => Modulus,
            Memory   => (1 .. Capacity => (V, 0, False)),
            Buckets  => (1 .. Modulus => 0),
            Free     => (if Capacity = 0 then 0 else -1),
            Length   => 0)
      do
         for B in 1 .. Modulus loop
            pragma Loop_Invariant (Num_Allocated (S.Buckets, S.Memory, B) = 0);
         end loop;
      end return;
   end Empty_Set;

   function Has_Element (S : Set; I : Positive_Count_Type) return Boolean is
      pragma
        Annotate
          (GNATprove,
           Hide_Info,
           "Expression_Function_Body",
           LL_Correct_Free_List);
      pragma
        Annotate
          (GNATprove, Hide_Info, "Expression_Function_Body", LL_Complete);
      pragma
        Annotate
          (GNATprove,
           Unhide_Info,
           "Expression_Function_Body",
           Values_From_Memory_Buckets);

      M : constant Set_LL_Model := LL_Model (S)
      with Ghost;
   begin
      pragma
        Assert
          (if I <= S.Capacity and then Is_Allocated (S.Buckets, S.Memory, I)
             then
               Find
                 (S.Memory,
                  S.Buckets (Find_Bucket (Get (M.Values, I), S.Modulus)),
                  I)
               > 0);
      return I <= S.Capacity and then S.Memory (I).Has_Element;
   end Has_Element;

   function Contains (S : Set; E : Element_Type) return Boolean is
      pragma
        Annotate
          (GNATprove,
           Hide_Info,
           "Expression_Function_Body",
           LL_Correct_Free_List);
      pragma
        Annotate
          (GNATprove, Hide_Info, "Expression_Function_Body", LL_Complete);
      pragma
        Annotate
          (GNATprove, Hide_Info, "Expression_Function_Body", LL_Has_Element);

      B        : constant Hash_Type := Find_Bucket (E, S.Modulus);
      Capacity : constant Count_Type := S.Capacity;
      C        : Count_Type range 0 .. Capacity := S.Buckets (B);
   begin
      while C /= 0 loop
         pragma Loop_Invariant (Well_Formed (C, S.Memory));
         pragma
           Loop_Invariant
             (LL_Sequence (C, S.Memory)
                <= LL_Sequence (S.Buckets (B), S.Memory));
         pragma
           Loop_Invariant
             (for all K in
                Interval'
                  (Last (LL_Sequence (C, S.Memory)) + 1,
                   Last (LL_Sequence (S.Buckets (B), S.Memory))) =>
                not Equivalent_Elements
                      (S.Memory (Get (LL_Sequence (S.Buckets (B), S.Memory), K))
                         .Value
                         .V,
                       E));
         pragma
           Loop_Variant (Decreases => Length (Reachable_Set (C, S.Memory)));
         if Equivalent_Elements (S.Memory (C).Value.V, E) then
            return True;
         end if;
         Lemma_Well_Formed_Def (C, S.Memory);
         Lemma_Reachable_Def (C, S.Memory);
         Lemma_LL_Sequence_Def (C, S.Memory);
         C := S.Memory (C).Next;
      end loop;
      return False;
   end Contains;

   function First (S : Set) return Count_Type is
      pragma
        Annotate
          (GNATprove,
           Hide_Info,
           "Expression_Function_Body",
           LL_Correct_Free_List);
      pragma
        Annotate
          (GNATprove, Hide_Info, "Expression_Function_Body", LL_Complete);
      pragma
        Annotate
          (GNATprove, Hide_Info, "Expression_Function_Body", LL_Has_Element);
      pragma
        Annotate
          (GNATprove,
           Hide_Info,
           "Expression_Function_Body",
           LL_Correct_Buckets_Value);

   begin
      if S.Length = 0 then
         return 0;
      end if;

      for B in 1 .. S.Modulus loop
         if S.Buckets (B) /= 0 then
            pragma Assert (Length (LL_Model (S).Buckets (B)) > 0);
            return S.Buckets (B);
         end if;
         pragma
           Loop_Invariant
             (for all K in 1 .. B =>
                Length (LL_Sequence (S.Buckets (K), S.Memory)) = 0);
         pragma Loop_Invariant (Num_Allocated (S.Buckets, S.Memory, B) = 0);
      end loop;

      raise Program_Error;
   end First;

   function Next (S : Set; I : Positive_Count_Type) return Count_Type is
      pragma
        Annotate
          (GNATprove,
           Hide_Info,
           "Expression_Function_Body",
           LL_Correct_Free_List);
      pragma
        Annotate
          (GNATprove, Hide_Info, "Expression_Function_Body", LL_Complete);
      pragma
        Annotate
          (GNATprove, Hide_Info, "Expression_Function_Body", LL_Has_Element);
      pragma
        Annotate
          (GNATprove,
           Hide_Info,
           "Expression_Function_Body",
           LL_Correct_Buckets_Value);

      B : constant Hash_Type := Find_Bucket (S.Memory (I).Value.V, S.Modulus)
      with Ghost;

      procedure Unfold_LL_Sequence
      with
        Ghost
        --  Iterate from S.Buckets (B) until I is found to link their models
      is
         C : Positive_Count_Type := S.Buckets (B);
      begin
         loop
            pragma Loop_Invariant (C <= S.Capacity);
            pragma Loop_Invariant (Well_Formed (C, S.Memory));
            pragma
              Loop_Invariant
                (LL_Sequence (C, S.Memory)
                   <= LL_Sequence (S.Buckets (B), S.Memory));
            pragma
              Loop_Invariant
                (for all K in
                   Interval'
                     (Last (LL_Sequence (C, S.Memory)) + 1,
                      Last (LL_Sequence (S.Buckets (B), S.Memory))) =>
                   Get (LL_Sequence (S.Buckets (B), S.Memory), K) /= I);
            pragma
              Loop_Variant (Decreases => Length (LL_Sequence (C, S.Memory)));
            Lemma_Well_Formed_Def (C, S.Memory);
            Lemma_LL_Sequence_Def (C, S.Memory);
            exit when C = I;
            C := S.Memory (C).Next;
         end loop;
         Lemma_LL_Sequence_Def (S.Memory (I).Next, S.Memory);
      end Unfold_LL_Sequence;

      B_N : Hash_Type range 1 .. S.Modulus;
   begin
      Unfold_LL_Sequence;

      if S.Memory (I).Next /= 0 then
         pragma Assert (Formal_Model.Find (LL_Model (S).Buckets (B), I) > 1);
         return S.Memory (I).Next;
      end if;

      B_N := Find_Bucket (S.Memory (I).Value.V, S.Modulus);

      while B_N < S.Modulus loop
         pragma Loop_Variant (Increases => B_N);
         pragma Loop_Invariant (B_N >= B);
         pragma
           Loop_Invariant
             (for all K in B + 1 .. B_N =>
                Length (LL_Sequence (S.Buckets (K), S.Memory)) = 0);
         B_N := B_N + 1;
         if S.Buckets (B_N) /= 0 then
            pragma Assert (Length (LL_Model (S).Buckets (B_N)) > 0);
            return S.Buckets (B_N);
         end if;
      end loop;
      return 0;
   end Next;

   procedure Allocate (S : in out Set; I : out Positive_Count_Type) is
      pragma
        Annotate
          (GNATprove,
           Hide_Info,
           "Expression_Function_Body",
           Values_From_Memory_Values);
      Old_S      : constant Set := S
      with Ghost;
      Old_Free   : constant Count_Type'Base := S.Free
      with Ghost;
      Old_Memory : constant Memory_Type := S.Memory
      with Ghost;

      procedure Prove_Invariant
      with
        Ghost
        --  Reestablish the invariant
      is
      begin
         --  The tail of the free list is preserved

         if Old_Free >= 0 then
            Lemma_Well_Formed_Def (Old_Free, Old_Memory);
            Lemma_Reachable_Def (Old_Free, Old_Memory);
            Lemma_LL_Sequence_Def (Old_Free, Old_Memory);
            Lemma_Well_Formed_Preserved (S.Free, Old_Memory, S.Memory);
            Lemma_Reachable_Preserved (S.Free, Old_Memory, S.Memory);
            Lemma_LL_Sequence_Preserved (S.Free, Old_Memory, S.Memory);
            pragma
              Assert
                (Is_Remove
                   (LL_Sequence (Old_Free, Old_Memory),
                    Last (LL_Sequence (Old_Free, Old_Memory)),
                    LL_Sequence (S.Free, S.Memory)));
         end if;
      end Prove_Invariant;

   begin
      Lemma_Length_Complete (S);
      if S.Free < 0 then
         I := -S.Free;
         if S.Free = -S.Capacity then
            S.Free := 0;
         else
            S.Free := S.Free - 1;
         end if;
      else
         I := S.Free;
         S.Free := S.Memory (S.Free).Next;
      end if;

      Prove_Invariant;
      Lemma_Values_Preserved (Old_S, S);
   end Allocate;

   procedure Deallocate (S : in out Set; I : Positive_Count_Type) is
      pragma
        Annotate
          (GNATprove,
           Hide_Info,
           "Expression_Function_Body",
           Values_From_Memory_Values);
      Old_S      : constant Set := S
      with Ghost;
      Old_Free   : constant Count_Type'Base := S.Free;
      Old_Memory : constant Memory_Type := S.Memory;

      procedure Prove_Expand_Free_List
      with
        --  Prove that we have preserved the free list after an expansion
        Ghost,
        Pre  =>
          S.Capacity > 0
          and then Old_Free < 0
          and then S.Memory (S.Capacity).Next = 0
          and then S.Free = I
          and then Old_Free >= -S.Capacity
          and then I < -Old_Free
          and then S.Memory (S.Free).Next = -Old_Free
          and then (for all L in -Old_Free .. S.Capacity - 1 =>
                      S.Memory (L).Next = L + 1),
        Post =>
          Well_Formed (S.Free, S.Memory)
          and then Is_Add
                     (All_From_Seq (-Old_Free - 1, S.Capacity),
                      I,
                      LL_Sequence (S.Free, S.Memory))
          and then (for all L of Reachable_Set (S.Free, S.Memory) =>
                      L in -Old_Free .. S.Capacity or else L = I)
          and then (for all L in -Old_Free .. S.Capacity =>
                      Reachable (S.Free, S.Memory, L))
          and then (Reachable (S.Free, S.Memory, I))
          and then (Length (Reachable_Set (S.Free, S.Memory))
                    = To_Big (S.Capacity + Old_Free + 2))
      is
      begin
         --  The tail of the free list is the extenion of the old free list

         for K in reverse -Old_Free .. S.Capacity loop
            Lemma_Well_Formed_Def (K, S.Memory);
            Lemma_Reachable_Def (K, S.Memory);
            Lemma_LL_Sequence_Def (K, S.Memory);
            pragma Loop_Invariant (Well_Formed (K, S.Memory));
            pragma
              Loop_Invariant
                (for all L of Reachable_Set (K, S.Memory) =>
                   L in K .. S.Capacity);
            pragma
              Loop_Invariant
                (for all L in K .. S.Capacity => Reachable (K, S.Memory, L));
            pragma
              Loop_Invariant
                (Length (Reachable_Set (K, S.Memory))
                   = To_Big (S.Capacity - K + 1));
            pragma
              Loop_Invariant
                (Length (LL_Sequence (K, S.Memory))
                   = To_Big (S.Capacity - K + 1));
            pragma
              Loop_Invariant
                (for all L in 1 .. Positive_Count_Type (S.Capacity - K + 1) =>
                   Get (LL_Sequence (K, S.Memory), To_Big (L))
                   = S.Capacity - L + 1);
         end loop;
         pragma
           Assert
             (for all L in
                1 .. Positive_Count_Type (S.Capacity + Old_Free + 1) =>
                Get (LL_Sequence (-Old_Free, S.Memory), To_Big (L))
                = Get (All_From_Seq (-Old_Free - 1, S.Capacity), To_Big (L)));
         pragma
           Assert
             (LL_Sequence (-Old_Free, S.Memory)
                = All_From_Seq (-Old_Free - 1, S.Capacity));

         --  I was added on top

         pragma Assert (S.Free = I and S.Memory (S.Free).Next = -Old_Free);
         Lemma_Well_Formed_Def (S.Free, S.Memory);
         Lemma_Reachable_Def (S.Free, S.Memory);
         Lemma_LL_Sequence_Def (S.Free, S.Memory);
      end Prove_Expand_Free_List;

      procedure Prove_Invariant
      with
        Ghost
        --  Reestablish the invariant
      is
      begin
         --  Go through the bucket list to prove that their LL_Sequence is preserved

         for B in 1 .. S.Modulus loop
            Lemma_Well_Formed_Preserved (S.Buckets (B), Old_Memory, S.Memory);
            Lemma_Reachable_Preserved (S.Buckets (B), Old_Memory, S.Memory);
            Lemma_LL_Sequence_Preserved (S.Buckets (B), Old_Memory, S.Memory);
            pragma
              Loop_Invariant
                (Num_Allocated (S.Buckets, S.Memory, B)
                   = Num_Allocated (S.Buckets, Old_Memory, B));
            pragma
              Loop_Invariant
                (for all I in 1 .. B => Well_Formed (S.Buckets (I), S.Memory));
            pragma
              Loop_Invariant
                (for all I in 1 .. B =>
                   Reachable_Set (S.Buckets (I), S.Memory)
                   = Reachable_Set (S.Buckets (I), Old_Memory));
            pragma
              Loop_Invariant
                (for all I in 1 .. B =>
                   LL_Sequence (S.Buckets (I), S.Memory)
                   = LL_Sequence (S.Buckets (I), Old_Memory));
            pragma
              Loop_Invariant
                (for all I in 1 .. B =>
                   Length (Reachable_Set (S.Buckets (I), S.Memory))
                   = Length (Reachable_Set (S.Buckets (I), Old_Memory)));
         end loop;
         pragma
           Assert
             (for all K in 1 .. S.Capacity =>
                Is_Allocated (S.Buckets, S.Memory, K)
                = Is_Allocated (S.Buckets, Old_Memory, K));

         --  Prove LL_Correct by case analysis

         if Old_Free >= 0 then
            pragma Assert (LL_Correct (S));
         elsif I + 1 = -Old_Free then
            pragma Assert (LL_Correct (S));
         else
            pragma Assert (LL_Correct (S));
         end if;
         pragma Assert (LL_Invariant (S));
      end Prove_Invariant;

   begin
      if S.Free >= 0 then
         S.Memory (I).Next := S.Free;
         S.Free := I;

         --  I has been added on top of the old free list

         Lemma_Well_Formed_Preserved (Old_Free, Old_Memory, S.Memory);
         Lemma_Reachable_Preserved (Old_Free, Old_Memory, S.Memory);
         Lemma_LL_Sequence_Preserved (Old_Free, Old_Memory, S.Memory);
         Lemma_Well_Formed_Def (S.Free, S.Memory);
         Lemma_Reachable_Def (S.Free, S.Memory);
         Lemma_LL_Sequence_Def (S.Free, S.Memory);
         pragma Assert (Well_Formed (S.Free, S.Memory));
         pragma
           Assert
             (Reachable_Set (S.Free, S.Memory)
                = Add (Reachable_Set (Old_Free, Old_Memory), I));
         pragma
           Assert
             (Is_Add
                (LL_Sequence (Old_Free, Old_Memory),
                 I,
                 LL_Sequence (S.Free, S.Memory)));
      elsif I + 1 = -S.Free then
         S.Free := S.Free + 1;
      else
         S.Memory (S.Capacity).Next := 0;
         for K in -S.Free .. S.Capacity - 1 loop
            S.Memory (K).Next := K + 1;
            pragma
              Loop_Invariant
                (for all L in -S.Free .. K => S.Memory (L).Next = L + 1);
         end loop;
         S.Memory (I).Next := -S.Free;
         S.Free := I;
         Prove_Expand_Free_List;
      end if;
      Prove_Invariant;
      Lemma_Values_Preserved (Old_S, S);
   end Deallocate;

   procedure Conditional_Insert
     (S        : in out Set;
      E        : Element_Type;
      I        : out Count_Type;
      Inserted : out Boolean)
   is
      B : constant Hash_Type := Find_Bucket (E, S.Modulus);

   begin
      I := S.Buckets (B);
      while I /= 0 loop
         pragma Loop_Invariant (I <= S.Capacity);
         pragma Loop_Invariant (Well_Formed (I, S.Memory));
         pragma
           Loop_Invariant
             (LL_Sequence (I, S.Memory)
                <= LL_Sequence (S.Buckets (B), S.Memory));
         pragma
           Loop_Invariant
             (for all K in
                Interval'
                  (Last (LL_Sequence (I, S.Memory)) + 1,
                   Last (LL_Sequence (S.Buckets (B), S.Memory))) =>
                not Equivalent_Elements
                      (S.Memory (Get (LL_Sequence (S.Buckets (B), S.Memory), K))
                         .Value
                         .V,
                       E));
         pragma
           Loop_Variant (Decreases => Length (Reachable_Set (I, S.Memory)));
         if Equivalent_Elements (S.Memory (I).Value.V, E) then
            pragma Assert (Find (S.Memory, S.Buckets (B), E) /= 0);
            Inserted := False;
            return;
         end if;
         Lemma_Well_Formed_Def (I, S.Memory);
         Lemma_Reachable_Def (I, S.Memory);
         Lemma_LL_Sequence_Def (I, S.Memory);
         I := S.Memory (I).Next;
      end loop;
      pragma
        Assert
          (for all K in
             Interval'(1, Last (LL_Sequence (S.Buckets (B), S.Memory))) =>
             not Equivalent_Elements
                   (S.Memory (Get (LL_Sequence (S.Buckets (B), S.Memory), K))
                      .Value
                      .V,
                    E));
      pragma Assert (Find (S.Memory, S.Buckets (B), E) = 0);

      Inserted := True;
      Allocate (S, I);
      Insert_Internal (S, I, E);
   end Conditional_Insert;

   procedure Insert_Internal
     (S : in out Set; I : Positive_Count_Type; E : Element_Type)
   is
      pragma
        Annotate
          (GNATprove,
           Unhide_Info,
           "Expression_Function_Body",
           Values_From_Memory_Buckets);

      B           : constant Hash_Type := Find_Bucket (E, S.Modulus);
      Old_S       : constant Set := S
      with Ghost;
      Old_Memory  : constant Memory_Type := S.Memory
      with Ghost;
      Old_Buckets : constant Bucket_Array := S.Buckets
      with Ghost;
      Old_Bucket  : constant Count_Type := S.Buckets (B)
      with Ghost;

      procedure Prove_Invariant
      with
        Ghost
        --  Reestablish the invariant
      is
      begin
         --  I was added to the bucket B

         Lemma_Well_Formed_Def (S.Buckets (B), S.Memory);
         Lemma_Well_Formed_Preserved (Old_Bucket, Old_Memory, S.Memory);
         Lemma_Reachable_Def (S.Buckets (B), S.Memory);
         Lemma_Reachable_Preserved (Old_Bucket, Old_Memory, S.Memory);
         Lemma_LL_Sequence_Def (S.Buckets (B), S.Memory);
         Lemma_LL_Sequence_Preserved (Old_Bucket, Old_Memory, S.Memory);
         pragma
           Assert
             (Reachable_Set (S.Buckets (B), S.Memory)
                = Add (Reachable_Set (Old_Bucket, Old_Memory), I));
         pragma
           Assert
             (Is_Add
                (LL_Sequence (Old_Bucket, Old_Memory),
                 I,
                 LL_Sequence (S.Buckets (B), S.Memory)));

         --  The free list is preserved

         if S.Free >= 0 then
            Lemma_Well_Formed_Preserved (S.Free, Old_Memory, S.Memory);
            Lemma_Reachable_Preserved (S.Free, Old_Memory, S.Memory);
            Lemma_LL_Sequence_Preserved (S.Free, Old_Memory, S.Memory);
         else
            pragma
              Assert
                (if S.Free < 0
                   then
                     (for all I in -S.Free .. S.Capacity =>
                        not Reachable (Old_Bucket, Old_Memory, I)));
            pragma
              Assert
                (if S.Free < 0
                   then
                     (for all I in -S.Free .. S.Capacity =>
                        not Reachable (S.Buckets (B), S.Memory, I)));
         end if;

         --  Go through the bucket list to prove that other buckets are preserved

         for K in 1 .. S.Modulus loop
            if B /= K then
               Lemma_Well_Formed_Preserved
                 (S.Buckets (K), Old_Memory, S.Memory);
               Lemma_Reachable_Preserved (S.Buckets (K), Old_Memory, S.Memory);
               Lemma_LL_Sequence_Preserved
                 (S.Buckets (K), Old_Memory, S.Memory);
            end if;
            pragma
              Loop_Invariant
                (if K < B
                   then
                     Num_Allocated (S.Buckets, S.Memory, K)
                     = Num_Allocated (Old_Buckets, Old_Memory, K)
                   else
                     Num_Allocated (S.Buckets, S.Memory, K)
                     = Num_Allocated (Old_Buckets, Old_Memory, K) + 1);
            pragma
              Loop_Invariant
                (for all I in 1 .. K => Well_Formed (S.Buckets (I), S.Memory));
            pragma
              Loop_Invariant
                (for all I in 1 .. K =>
                   (if I /= B
                    then
                      Reachable_Set (S.Buckets (I), S.Memory)
                      = Reachable_Set (S.Buckets (I), Old_Memory)));
            pragma
              Loop_Invariant
                (for all I in 1 .. K =>
                   (if I /= B
                    then
                      LL_Sequence (S.Buckets (I), Old_Memory)
                      = LL_Sequence (S.Buckets (I), S.Memory)));
            pragma
              Loop_Invariant
                (for all I in 1 .. K =>
                   (if I /= B
                    then
                      Length (Reachable_Set (S.Buckets (I), S.Memory))
                      = Length (Reachable_Set (S.Buckets (I), Old_Memory))));
         end loop;

         pragma
           Assert
             (for all K in 1 .. S.Capacity =>
                (if K /= I
                 then
                   Is_Allocated (S.Buckets, S.Memory, K)
                   = Is_Allocated (Old_Buckets, Old_Memory, K)));
         pragma Assert (LL_Correct (S));
      end Prove_Invariant;

   begin
      --  pragma Assert (not Has_Key (LL_Model (Old_S).Values, I));
      S.Memory (I) := ((V => E), S.Buckets (B), True);
      S.Buckets (B) := I;
      S.Length := S.Length + 1;

      Prove_Invariant;
      Lemma_Values_Preserved (Old_S, S, I);
   end Insert_Internal;

   procedure Delete_No_Free (S : in out Set; I : Positive_Count_Type) is
      B           : constant Hash_Type :=
        Find_Bucket (S.Memory (I).Value.V, S.Modulus);
      Old_S       : constant Set := S
      with Ghost;
      Old_Memory  : constant Memory_Type := S.Memory
      with Ghost;
      Old_Buckets : constant Bucket_Array := S.Buckets
      with Ghost;
      Old_Bucket  : constant Positive_Count_Type := S.Buckets (B)
      with Ghost;

      procedure Prove_Invariant
      with
        Ghost
        --  Reestablish the invariant
      is
      begin
         --  The free list is preserved

         if S.Free >= 0 then
            Lemma_Well_Formed_Preserved (S.Free, Old_Memory, S.Memory);
            Lemma_Reachable_Preserved (S.Free, Old_Memory, S.Memory);
            Lemma_LL_Sequence_Preserved (S.Free, Old_Memory, S.Memory);
         end if;

         --  Go through the bucket list to prove that other buckets are preserved

         pragma
           Assert
             (for all K in 1 .. S.Modulus =>
                (if K /= B then not Reachable (S.Buckets (K), Old_Memory, I)));

         for K in 1 .. S.Modulus loop
            if K /= B then
               Lemma_Well_Formed_Preserved
                 (S.Buckets (K), Old_Memory, S.Memory);
               Lemma_Reachable_Preserved (S.Buckets (K), Old_Memory, S.Memory);
               Lemma_LL_Sequence_Preserved
                 (S.Buckets (K), Old_Memory, S.Memory);
            else
               pragma
                 Assert
                   (By
                      (Num_Allocated (S.Buckets, S.Memory, K)
                       = Num_Allocated (Old_Buckets, Old_Memory, K) - 1,
                       Length (Reachable_Set (S.Buckets (B), S.Memory))
                       = Length (Reachable_Set (Old_Buckets (B), Old_Memory))
                         - 1));
            end if;
            pragma
              Loop_Invariant
                (if K < B
                   then
                     Num_Allocated (S.Buckets, S.Memory, K)
                     = Num_Allocated (Old_Buckets, Old_Memory, K)
                   else
                     Num_Allocated (S.Buckets, S.Memory, K)
                     = Num_Allocated (Old_Buckets, Old_Memory, K) - 1);
            pragma
              Loop_Invariant
                (for all I in 1 .. K => Well_Formed (S.Buckets (I), S.Memory));
            pragma
              Loop_Invariant
                (for all I in 1 .. K =>
                   (if I /= B
                    then
                      Reachable_Set (S.Buckets (I), S.Memory)
                      = Reachable_Set (S.Buckets (I), Old_Memory)));
            pragma
              Loop_Invariant
                (for all I in 1 .. K =>
                   (if I /= B
                    then
                      LL_Sequence (S.Buckets (I), Old_Memory)
                      = LL_Sequence (S.Buckets (I), S.Memory)));
            pragma
              Loop_Invariant
                (for all I in 1 .. K =>
                   (if I /= B
                    then
                      Length (Reachable_Set (S.Buckets (I), S.Memory))
                      = Length (Reachable_Set (S.Buckets (I), Old_Memory))));
         end loop;

         pragma
           Assert
             (for all K in 1 .. S.Capacity =>
                (if K /= I
                 then
                   Is_Allocated (S.Buckets, S.Memory, K)
                   = Is_Allocated (Old_Buckets, Old_Memory, K)));
         pragma Assert (LL_Correct (S));
      end Prove_Invariant;

   begin
      if I = S.Buckets (B) then
         Lemma_Well_Formed_Def (I, S.Memory);
         Lemma_Reachable_Def (I, S.Memory);
         Lemma_LL_Sequence_Def (I, S.Memory);

         S.Buckets (B) := S.Memory (I).Next;
         S.Memory (I).Has_Element := False;

         --  I has been removed from S.Buckets (B)

         Lemma_Well_Formed_Preserved (S.Buckets (B), Old_Memory, S.Memory);
         Lemma_Reachable_Preserved (S.Buckets (B), Old_Memory, S.Memory);
         Lemma_LL_Sequence_Preserved (S.Buckets (B), Old_Memory, S.Memory);
         pragma Assert (Well_Formed (S.Buckets (B), S.Memory));
         pragma
           Assert
             (Reachable_Set (S.Buckets (B), S.Memory)
                = Remove (Reachable_Set (Old_Bucket, Old_Memory), I));
         pragma
           Assert
             (Is_Remove
                (LL_Sequence (Old_Bucket, Old_Memory),
                 Formal_Model.Find (LL_Sequence (Old_Bucket, Old_Memory), I),
                 LL_Sequence (S.Buckets (B), S.Memory)));
      else
         declare
            Capacity : constant Count_Type := S.Capacity;
            C        : Positive_Count_Type range 1 .. Capacity := S.Buckets (B);
            N        : Positive_Count_Type range 1 .. Capacity;
         begin
            loop

               --  We are traversing the list rooted at S.Buckets (B) in
               --  S.Memory.

               pragma Loop_Invariant (Well_Formed (C, S.Memory));
               pragma
                 Loop_Invariant
                   (Reachable_Set (C, S.Memory)
                      <= Reachable_Set (S.Buckets (B), S.Memory));
               pragma
                 Loop_Invariant
                   (LL_Sequence (C, S.Memory)
                      <= LL_Sequence (S.Buckets (B), S.Memory));

               --  I has not been reached yet

               pragma Loop_Invariant (C /= I);
               pragma Loop_Invariant (Reachable (C, S.Memory, I));
               pragma
                 Loop_Invariant
                   (for all K in
                      Interval'
                        (Last (LL_Sequence (C, S.Memory)),
                         Last (LL_Sequence (S.Buckets (B), S.Memory))) =>
                      Get (LL_Sequence (S.Buckets (B), S.Memory), K) /= I);

               pragma
                 Loop_Variant
                   (Decreases => Length (Reachable_Set (C, S.Memory)));

               Lemma_Well_Formed_Def (C, S.Memory);
               Lemma_Reachable_Def (C, S.Memory);
               Lemma_LL_Sequence_Def (C, S.Memory);

               N := S.Memory (C).Next;
               exit when N = I;
               C := N;
            end loop;
            pragma
              Assert
                (Last (LL_Sequence (N, S.Memory))
                   = Formal_Model.Find
                       (LL_Sequence (Old_Bucket, Old_Memory), I));
            Lemma_Well_Formed_Def (I, S.Memory);
            Lemma_Reachable_Def (I, S.Memory);
            Lemma_LL_Sequence_Def (I, S.Memory);

            S.Memory (C).Next := S.Memory (I).Next;
            S.Memory (I).Has_Element := False;

            --  I has been removed from S.Buckets (B)

            Lemma_Well_Formed_Set
              (S.Buckets (B), C, S.Memory (I).Next, Old_Memory, S.Memory);
            Lemma_Reachable_Set
              (S.Buckets (B), C, S.Memory (I).Next, Old_Memory, S.Memory);
            Lemma_LL_Sequence_Set
              (S.Buckets (B), C, S.Memory (I).Next, Old_Memory, S.Memory);
            pragma Assert (Well_Formed (S.Buckets (B), S.Memory));
            pragma
              Assert
                (Reachable_Set (S.Buckets (B), S.Memory)
                   = Remove (Reachable_Set (S.Buckets (B), Old_Memory), I));
            pragma
              Assert
                (Is_Remove
                   (LL_Sequence (Old_Bucket, Old_Memory),
                    Formal_Model.Find (LL_Sequence (Old_Bucket, Old_Memory), I),
                    LL_Sequence (S.Buckets (B), S.Memory)));

         end;
      end if;
      Prove_Invariant;
      S.Length := S.Length - 1;

      Lemma_Values_Preserved (Old_S, S, I);
      Lemma_Values_Buckets (S, B, I);
      Lemma_Values_Buckets (Old_S, B, I);
   end Delete_No_Free;

   procedure Delete (S : in out Set; I : Positive_Count_Type) is
      pragma
        Annotate
          (GNATprove,
           Hide_Info,
           "Expression_Function_Body",
           LL_Correct_Free_List);
      pragma
        Annotate
          (GNATprove, Hide_Info, "Expression_Function_Body", LL_Complete);
      pragma
        Annotate
          (GNATprove, Hide_Info, "Expression_Function_Body", LL_Has_Element);

      B          : constant Hash_Type :=
        Find_Bucket (S.Memory (I).Value.V, S.Modulus)
      with Ghost;
      Old_Bucket : constant Sequence := LL_Model (S).Buckets (B)
      with Ghost;
   begin
      Delete_No_Free (S, I);
      Deallocate (S, I);
   end Delete;

   procedure Delete_Key_No_Free
     (S : in out Set; E : Element_Type; I : out Count_Type)
   is
      B           : constant Hash_Type := Find_Bucket (E, S.Modulus);
      Old_S       : constant Set := S
      with Ghost;
      Old_Memory  : constant Memory_Type := S.Memory
      with Ghost;
      Old_Buckets : constant Bucket_Array := S.Buckets
      with Ghost;
      Old_Bucket  : constant Count_Type := S.Buckets (B)
      with Ghost;
      Pos         : constant Big_Natural := Find (S.Memory, S.Buckets (B), E)
      with Ghost;
      pragma
        Assert
          (Pos
             = Formal_Model.Find
                 (LL_Model (S).Buckets (Find_Bucket (E, S.Modulus)),
                  LL_Model (S).Values,
                  E));

      procedure Prove_Invariant
      with
        Ghost
        --  Reestablish the invariant
      is
      begin
         --  Go through the bucket list to prove that other buckets are preserved

         for K in 1 .. S.Modulus loop
            if K /= B then
               Lemma_Well_Formed_Preserved
                 (S.Buckets (K), Old_Memory, S.Memory);
               Lemma_Reachable_Preserved (S.Buckets (K), Old_Memory, S.Memory);
               Lemma_LL_Sequence_Preserved
                 (S.Buckets (K), Old_Memory, S.Memory);
            end if;
            pragma
              Loop_Invariant
                (if K < B
                   then
                     Num_Allocated (S.Buckets, S.Memory, K)
                     = Num_Allocated (Old_Buckets, Old_Memory, K)
                   else
                     Num_Allocated (S.Buckets, S.Memory, K)
                     = Num_Allocated (Old_Buckets, Old_Memory, K) - 1);
            pragma
              Loop_Invariant
                (for all I in 1 .. K => Well_Formed (S.Buckets (I), S.Memory));
            pragma
              Loop_Invariant
                (for all I in 1 .. K =>
                   (if I /= B
                    then
                      Reachable_Set (S.Buckets (I), Old_Memory)
                      = Reachable_Set (S.Buckets (I), S.Memory)));
            pragma
              Loop_Invariant
                (for all I in 1 .. K =>
                   (if I /= B
                    then
                      LL_Sequence (S.Buckets (I), Old_Memory)
                      = LL_Sequence (S.Buckets (I), S.Memory)));
            pragma
              Loop_Invariant
                (for all I in 1 .. K =>
                   (if I /= B
                    then
                      Length (Reachable_Set (S.Buckets (I), S.Memory))
                      = Length (Reachable_Set (S.Buckets (I), Old_Memory))));
         end loop;

         --  The free list is preserved

         if S.Free >= 0 then
            Lemma_Well_Formed_Preserved (S.Free, Old_Memory, S.Memory);
            Lemma_Reachable_Preserved (S.Free, Old_Memory, S.Memory);
            Lemma_LL_Sequence_Preserved (S.Free, Old_Memory, S.Memory);
            pragma
              Assert
                (Reachable_Set (S.Free, S.Memory)
                   = Reachable_Set (S.Free, Old_Memory));
         end if;

         pragma
           Assert
             (for all K in 1 .. S.Capacity =>
                (if K /= I
                 then
                   Reachable (S.Buckets (B), S.Memory, K)
                   = Reachable (S.Buckets (B), Old_Memory, K)));
         pragma
           Assert
             (for all K of Reachable_Set (S.Buckets (B), S.Memory) =>
                S.Memory (K).Value'Initialized);
         pragma Assert (LL_Correct_Free_List (S));
         pragma Assert (LL_Correct (S));
         pragma
           Assert
             (for all K in 1 .. S.Capacity =>
                (if K /= I
                 then
                   Is_Allocated (S.Buckets, S.Memory, K)
                   = Is_Allocated (Old_Buckets, Old_Memory, K)));
         pragma Assert (LL_Has_Element (S));
         Lemma_Values_Preserved (Old_S, S, I);
         Lemma_Values_Buckets (Old_S, B, I);
         Lemma_Values_Buckets (S, B, I);
      end Prove_Invariant;

      procedure Prove_Length
      with
        Ghost,
        Pre  =>
          B in 1 .. S.Modulus and then LL_Correct (S) and then LL_Length (S),
        Post => (if Find (S.Memory, S.Buckets (B), E) /= 0 then S.Length > 0)
      is
         pragma
           Annotate
             (GNATprove,
              Hide_Info,
              "Expression_Function_Body",
              LL_Correct_Free_List);
      begin
         for K in B .. S.Modulus loop
            pragma
              Loop_Invariant
                (if Find (S.Memory, S.Buckets (B), E) /= 0
                   then Num_Allocated (S.Buckets, S.Memory, K) > 0);
         end loop;
      end Prove_Length;

   begin

      --  Show that there is at least an allocated cell if E is in the set

      Prove_Length;

      I := S.Buckets (B);

      if I = 0 then
         pragma Assert (Pos = 0);
         return;
      end if;

      if Equivalent_Elements (S.Memory (S.Buckets (B)).Value.V, E) then
         Lemma_Well_Formed_Def (I, S.Memory);
         Lemma_Reachable_Def (I, S.Memory);
         Lemma_LL_Sequence_Def (I, S.Memory);

         S.Buckets (B) := S.Memory (I).Next;
         S.Memory (I).Has_Element := False;

         --  I has been removed from S.Buckets (B)

         Lemma_Well_Formed_Preserved (S.Buckets (B), Old_Memory, S.Memory);
         Lemma_Reachable_Preserved (S.Buckets (B), Old_Memory, S.Memory);
         Lemma_LL_Sequence_Preserved (S.Buckets (B), Old_Memory, S.Memory);
         pragma Assert (Well_Formed (S.Buckets (B), S.Memory));
         pragma
           Assert
             (Reachable_Set (S.Buckets (B), S.Memory)
                = Remove (Reachable_Set (I, Old_Memory), I));
         pragma
           Assert
             (Is_Remove
                (LL_Sequence (I, Old_Memory),
                 Find (Old_Memory, I, I),
                 LL_Sequence (S.Buckets (B), S.Memory)));
      else
         declare
            Capacity : constant Count_Type := S.Capacity;
            P        : Positive_Count_Type range 1 .. Capacity;
         begin
            loop

               --  We are traversing the list rooted at S.Buckets (B) in
               --  S.Memory.

               pragma Loop_Invariant (I /= 0 and I <= S.Capacity);
               pragma Loop_Invariant (Well_Formed (I, S.Memory));
               pragma
                 Loop_Invariant
                   (Reachable_Set (I, S.Memory)
                      <= Reachable_Set (S.Buckets (B), S.Memory));
               pragma
                 Loop_Invariant
                   (LL_Sequence (I, S.Memory)
                      <= LL_Sequence (S.Buckets (B), S.Memory));

               --  E has not been found yet

               pragma
                 Loop_Invariant
                   (not Equivalent_Elements (S.Memory (I).Value.V, E));
               pragma
                 Loop_Invariant
                   (for all K in
                      Interval'
                        (Last (LL_Sequence (I, S.Memory)),
                         Last (LL_Sequence (S.Buckets (B), S.Memory))) =>
                      not Equivalent_Elements
                            (S.Memory
                               (Get (LL_Sequence (S.Buckets (B), S.Memory), K))
                               .Value
                               .V,
                             E));

               pragma
                 Loop_Variant
                   (Decreases => Length (Reachable_Set (I, S.Memory)));

               Lemma_Well_Formed_Def (I, S.Memory);
               Lemma_Reachable_Def (I, S.Memory);
               Lemma_LL_Sequence_Def (I, S.Memory);

               P := I;
               I := S.Memory (I).Next;
               if I = 0 then
                  pragma Assert (Pos = 0);
                  return;
               elsif Equivalent_Elements (S.Memory (I).Value.V, E) then
                  pragma Assert (Pos = Last (LL_Sequence (I, S.Memory)));

                  S.Memory (P).Next := S.Memory (I).Next;
                  S.Memory (I).Has_Element := False;

                  --  I has been removed from S.Buckets (B)

                  begin
                     Lemma_Well_Formed_Def (I, Old_Memory);
                     Lemma_Reachable_Def (I, Old_Memory);
                     Lemma_LL_Sequence_Def (I, Old_Memory);
                     Lemma_Well_Formed_Set
                       (S.Buckets (B),
                        P,
                        S.Memory (I).Next,
                        Old_Memory,
                        S.Memory);
                     Lemma_Reachable_Set
                       (S.Buckets (B),
                        P,
                        S.Memory (I).Next,
                        Old_Memory,
                        S.Memory);
                     Lemma_LL_Sequence_Set
                       (S.Buckets (B),
                        P,
                        S.Memory (I).Next,
                        Old_Memory,
                        S.Memory);
                     pragma
                       Assert
                         (Range_Shifted
                            (LL_Sequence (S.Buckets (B), S.Memory),
                             LL_Sequence (S.Buckets (B), Old_Memory),
                             Pos,
                             Last (LL_Sequence (S.Buckets (B), S.Memory)),
                             1));
                     pragma
                       Assert_And_Cut
                         (Well_Formed (S.Buckets (B), S.Memory)
                            and Reachable_Set (S.Buckets (B), S.Memory)
                                = Remove
                                    (Reachable_Set (S.Buckets (B), Old_Memory),
                                     I)
                            and Is_Remove
                                  (LL_Sequence (S.Buckets (B), Old_Memory),
                                   Pos,
                                   LL_Sequence (S.Buckets (B), S.Memory)));
                  end;
                  exit;
               end if;
            end loop;
         end;
      end if;

      S.Length := S.Length - 1;
      Prove_Invariant;
   end Delete_Key_No_Free;

   procedure Delete_Key (S : in out Set; E : Element_Type) is
      pragma
        Annotate (GNATprove, Hide_Info, "Expression_Function_Body", LL_Model);
      pragma
        Annotate (GNATprove, Hide_Info, "Expression_Function_Body", LL_Correct);
      pragma
        Annotate
          (GNATprove, Hide_Info, "Expression_Function_Body", LL_Complete);
      pragma
        Annotate
          (GNATprove, Hide_Info, "Expression_Function_Body", LL_Has_Element);

      Old_M    : constant Sequence :=
        LL_Model (S).Buckets (Find_Bucket (E, S.Modulus))
      with Ghost;
      P        : constant Big_Natural :=
        Find
          (LL_Model (S).Buckets (Find_Bucket (E, S.Modulus)),
           LL_Model (S).Values,
           E)
      with Ghost;
      Capacity : constant Count_Type := S.Capacity;
      I        : Count_Type range 0 .. Capacity;
   begin
      Delete_Key_No_Free (S, E, I);
      if I > 0 then
         Deallocate (S, I);
         pragma
           Assert
             (Is_Remove
                (Old_M, P, LL_Model (S).Buckets (Find_Bucket (E, S.Modulus))));
      end if;
   end Delete_Key;

   procedure Replace_Element
     (S : in out Set; I : Positive_Count_Type; E : Element_Type)
   is
      Old_S      : constant Set := S
      with Ghost;
      Old_Memory : constant Memory_Type := S.Memory
      with Ghost;

      procedure Prove_Invariant
      with
        Ghost
        --  Reestablish the invariant in the case where the bucket is not changed
      is
      begin
         --  The free list is preserved

         if S.Free >= 0 then
            Lemma_Well_Formed_Preserved (S.Free, Old_Memory, S.Memory);
            Lemma_Reachable_Preserved (S.Free, Old_Memory, S.Memory);
            Lemma_LL_Sequence_Preserved (S.Free, Old_Memory, S.Memory);
            pragma
              Assert
                (Reachable_Set (S.Free, Old_Memory)
                   = Reachable_Set (S.Free, Old_Memory));
         end if;

         --  Go through the bucket list to prove that buckets are preserved

         for K in 1 .. S.Modulus loop
            Lemma_Well_Formed_Preserved (S.Buckets (K), Old_Memory, S.Memory);
            Lemma_Reachable_Preserved (S.Buckets (K), Old_Memory, S.Memory);
            Lemma_LL_Sequence_Preserved (S.Buckets (K), Old_Memory, S.Memory);
            pragma
              Loop_Invariant
                (Num_Allocated (S.Buckets, S.Memory, K)
                   = Num_Allocated (S.Buckets, Old_Memory, K));
            pragma
              Loop_Invariant
                (for all I in 1 .. K => Well_Formed (S.Buckets (I), S.Memory));
            pragma
              Loop_Invariant
                (for all I in 1 .. K =>
                   Reachable_Set (S.Buckets (I), S.Memory)
                   = Reachable_Set (S.Buckets (I), Old_Memory));
            pragma
              Loop_Invariant
                (for all I in 1 .. K =>
                   LL_Sequence (S.Buckets (I), Old_Memory)
                   = LL_Sequence (S.Buckets (I), S.Memory));
            pragma
              Loop_Invariant
                (for all I in 1 .. K =>
                   Length (Reachable_Set (S.Buckets (I), S.Memory))
                   = Length (Reachable_Set (S.Buckets (I), Old_Memory)));
         end loop;

         pragma
           Assert
             (for all K in 1 .. S.Capacity =>
                Is_Allocated (S.Buckets, S.Memory, K)
                = Is_Allocated (S.Buckets, Old_Memory, K));
         pragma Assert (LL_Invariant (S));
         Lemma_Values_Preserved (Old_S, S, I);
         Lemma_Values_Buckets (S, Find_Bucket (E, S.Modulus), I);
         Lemma_Values_Buckets (Old_S, Find_Bucket (E, S.Modulus), I);
      end Prove_Invariant;

   begin
      Lemma_Equivalent_Elements_Find_Bucket
        (S.Memory (I).Value.V, E, S.Modulus);

      if Find_Bucket (S.Memory (I).Value.V, S.Modulus)
        = Find_Bucket (E, S.Modulus)
      then
         S.Memory (I).Value := (V => E);
         Prove_Invariant;
         return;
      end if;

      declare
         Capacity : constant Count_Type := S.Capacity;
         C        : Count_Type range 0 .. Capacity :=
           S.Buckets (Find_Bucket (E, S.Modulus));
      begin
         while C /= 0 loop
            pragma Loop_Invariant (Well_Formed (C, S.Memory));
            pragma
              Loop_Invariant
                (LL_Sequence (C, S.Memory)
                   <= LL_Sequence
                        (S.Buckets (Find_Bucket (E, S.Modulus)), S.Memory));
            pragma
              Loop_Variant (Decreases => Length (LL_Sequence (C, S.Memory)));
            if Equivalent_Elements (S.Memory (C).Value.V, E) then
               raise Program_Error with "attempt to replace existing element";
            end if;
            Lemma_Well_Formed_Def (C, S.Memory);
            Lemma_LL_Sequence_Def (C, S.Memory);
            C := S.Memory (C).Next;
         end loop;
      end;

      Delete_No_Free (S, I);
      Insert_Internal (S, I, E);
   end Replace_Element;

end Data_Structure.Basic_Operations;
