with SPARK.Higher_Order.Reachability;
with SPARK.Big_Intervals;  use SPARK.Big_Intervals;
with SPARK.Cut_Operations; use SPARK.Cut_Operations;

package body Data_Structure.Basic_Operations
  with SPARK_Mode
is

   package Private_Model
     with Ghost
   is

      function Node_Preserved (X, Y : Node_Type) return Boolean
      with
        Import,
        Ghost,
        Global   => null,
        Annotate => (GNATprove, Logical_Equal);
      --  Logical equality on nodes. It is used to state that some nodes are
      --  preserved by procedure calls. It is not executable as the element in
      --  the cell might not be initialized.

      package Memory_Index_Sets is new
        SPARK.Containers.Functional.Sets (Positive_Count_Type);
      use Memory_Index_Sets;
      subtype Memory_Index_Set is Memory_Index_Sets.Set;

      function Next (X : Node_Type) return Count_Type
      is (X.Next)
      with Annotate => (GNATprove, Inline_For_Proof);

      package Node_Reachability is new
        SPARK.Higher_Order.Reachability
          (Positive_Count_Type,
           0,
           Node_Type,
           Nodes_Type_Base,
           Next,
           Memory_Index_Sets,
           Memory_Index_Sequences,
           Automatically_Instantiate_Definitions => False);
      use Node_Reachability;

      function LL_Sequence (X : Count_Type; M : Nodes_Type) return Sequence
      renames Node_Reachability.Model;
      procedure Lemma_LL_Sequence_Def (X : Count_Type; M : Nodes_Type)
      renames Node_Reachability.Lemma_Model_Def;
      procedure Lemma_LL_Sequence_Preserved
        (X : Count_Type; M1, M2 : Nodes_Type)
      renames Node_Reachability.Lemma_Model_Preserved;
      procedure Lemma_LL_Sequence_Set
        (X, Y : Positive_Count_Type; Z : Count_Type; M1, M2 : Nodes_Type)
      renames Node_Reachability.Lemma_Model_Set;

      --  Invariant: The buckets and free lists are acyclic and they do not
      --  overlap.

      function LL_Correct_Is_Acyclic_Buckets (S : Set) return Boolean
      is (for all B1 in S.Buckets'Range =>
            Is_Acyclic (S.Buckets (B1), S.Nodes));

      function LL_Correct_Buckets_Element (S : Set) return Boolean
      is ((for all B in S.Buckets'Range =>
             (for all I of Reachable_Set (S.Buckets (B), S.Nodes) =>
                S.Nodes (I).Element'Initialized))
          and then
            (for all B in S.Buckets'Range =>
               (for all I of Reachable_Set (S.Buckets (B), S.Nodes) =>
                  Find_Bucket (S.Nodes (I).Element.V, S.Modulus) = B)));

      function LL_Correct_Free_List (S : Set) return Boolean
      is ((if S.Free >= 0 then Is_Acyclic (S.Free, S.Nodes))
          and then
            (if S.Free >= 0
             then
               (for all I of Reachable_Set (S.Free, S.Nodes) =>
                  (for all B in S.Buckets'Range =>
                     not Reachable (S.Buckets (B), S.Nodes, I)))
             else
               (for all I in -S.Free .. S.Capacity =>
                  (for all B in S.Buckets'Range =>
                     not Reachable (S.Buckets (B), S.Nodes, I)))));

      function Values_From_Nodes_Buckets
        (S : Set; Values : Values_Type) return Boolean
      is ((for all I of Values =>
             I <= S.Capacity
             and then
               Reachable
                 (S.Buckets (Find_Bucket (Get (Values, I), S.Modulus)),
                  S.Nodes,
                  I))
          and then
            (for all B in S.Buckets'Range =>
               (for all I of Reachable_Set (S.Buckets (B), S.Nodes) =>
                  Has_Key (Values, I))));

      function Values_From_Nodes_Values
        (S : Set; Values : Values_Type) return Boolean
      is ((for all I of Values =>
             I <= S.Capacity and then S.Nodes (I).Element'Initialized)
          and then
            (for all I of Values => S.Nodes (I).Element.V = Get (Values, I)));

      function Values_From_Nodes (S : Set) return Values_Type
      with
        Pre  =>
          LL_Correct_Is_Acyclic_Buckets (S)
          and then LL_Correct_Buckets_Element (S),
        Post =>
          Values_From_Nodes_Buckets (S, Values_From_Nodes'Result)
          and then Values_From_Nodes_Values (S, Values_From_Nodes'Result);
      --  Construct the Element map from Nodes

      --  Proves that reachability in bucket B corresponds to membership in
      --  the values map.
      procedure Lemma_Values_Buckets
        (S : Set; B : Positive_Hash_Type; I : Positive_Count_Type)
      with
        Pre  =>
          LL_Correct_Is_Acyclic_Buckets (S)
          and then LL_Correct_Buckets_Element (S)
          and then B <= S.Modulus
          and then I <= S.Capacity,
        Post =>
          (if Reachable (S.Buckets (B), S.Nodes, I)
           then Has_Key (Values_From_Nodes (S), I))
          and
            (if Has_Key (Values_From_Nodes (S), I)
               and then B = Find_Bucket (S.Nodes (I).Element.V, S.Modulus)
             then Reachable (S.Buckets (B), S.Nodes, I));

      --  Proves the values map is shared between two sets whose allocated
      --  nodes agree except possibly at I.
      procedure Lemma_Values_Preserved (S1, S2 : Set; I : Count_Type := 0)
      with
        Pre  =>
          LL_Correct_Is_Acyclic_Buckets (S1)
          and then LL_Correct_Buckets_Element (S1)
          and then LL_Correct_Is_Acyclic_Buckets (S2)
          and then LL_Correct_Buckets_Element (S2)
          and then I <= S1.Capacity
          and then S1.Capacity = S2.Capacity
          and then S1.Modulus = S2.Modulus
          and then
            (for all B in 1 .. S1.Modulus =>
               (for all J in 1 .. S1.Capacity =>
                  (if I /= J
                   then
                     Contains (Reachable_Set (S1.Buckets (B), S1.Nodes), J)
                     = Contains
                         (Reachable_Set (S2.Buckets (B), S2.Nodes), J))))
          and then
            (for all B in 1 .. S1.Modulus =>
               (for all J of Reachable_Set (S1.Buckets (B), S1.Nodes) =>
                  (if I /= J
                   then S1.Nodes (J).Element.V = S2.Nodes (J).Element.V))),
        Post =>
          (for all J of Values_From_Nodes (S1) =>
             (if I /= J then Has_Key (Values_From_Nodes (S2), J)))
          and then
            (for all J of Values_From_Nodes (S2) =>
               (if I /= J then Has_Key (Values_From_Nodes (S1), J)))
          and then
            (for all J of Values_From_Nodes (S2) =>
               (if I /= J
                then
                  Get (Values_From_Nodes (S1), J)
                  = Get (Values_From_Nodes (S2), J)));

      --  Invariant: The buckets and free lists cover the whole Nodes

      function Is_Allocated
        (Buckets : Buckets_Type; M : Nodes_Type; I : Positive_Count_Type)
         return Boolean
      is (M (I).Element'Initialized
          and then
            Reachable
              (Buckets (Find_Bucket (M (I).Element.V, Buckets'Last)), M, I))
      with
        Pre =>
          I <= M'Last
          and then Buckets'Last >= 1
          and then (for all B of Buckets => B <= M'Last);

      function Is_Free
        (Free : Count_Type'Base; M : Nodes_Type; I : Positive_Count_Type)
         return Boolean
      is (if Free >= 0 then Reachable (Free, M, I) else I >= -Free)
      with Pre => I <= M'Last and then Free in -M'Last .. M'Last;

      function LL_Complete (S : Set) return Boolean
      is (for all I in S.Nodes'Range =>
            Is_Free (S.Free, S.Nodes, I)
            or else Is_Allocated (S.Buckets, S.Nodes, I));

      --  Invariant: The Has_Element field of each node is set iff the node
      --  is allocated.

      function LL_Has_Element (S : Set) return Boolean
      is (for all I in S.Nodes'Range =>
            Is_Allocated (S.Buckets, S.Nodes, I) = S.Nodes (I).Has_Element);

      --  Invariant: The Length component is the number of allocated cells

      --  Total number of nodes allocated in buckets 1 .. B
      function Num_Allocated
        (Buckets : Buckets_Type; M : Nodes_Type; B : Hash_Type)
         return Big_Natural
      with
        Subprogram_Variant => (Decreases => B),
        Pre                =>
          B in Buckets'Range
          and then Buckets'Last >= 1
          and then (for all B of Buckets => B <= M'Last);

      function Num_Allocated
        (Buckets : Buckets_Type; M : Nodes_Type; B : Hash_Type)
         return Big_Natural
      is (Length (Reachable_Set (Buckets (B), M))
          + (if B = 1 then 0 else Num_Allocated (Buckets, M, B - 1)));

      function Num_Allocated (S : Set) return Big_Natural
      is (Num_Allocated (S.Buckets, S.Nodes, S.Modulus));

      --  Proves the allocated-node count equals capacity minus the number
      --  of free nodes.
      procedure Lemma_Length_Complete (S : Set)
      with
        Ghost,
        Pre  => LL_Correct (S) and LL_Complete (S),
        Post =>
          (if S.Free >= 0
           then
             Num_Allocated (S)
             = To_Big (S.Capacity) - Length (Reachable_Set (S.Free, S.Nodes))
           else Num_Allocated (S) = To_Big (-S.Free - 1));

      function LL_Length (S : Set) return Boolean
      is (To_Big (S.Length) = Num_Allocated (S));

      --  Special sequences used in specifications

      function Empty_Seq return Sequence
      with Post => Length (Empty_Seq'Result) = 0;

      --  Returns a sequence of the integers Fst+1 .. Lst in decreasing order
      function All_From_Seq (Fst, Lst : Count_Type) return Sequence
      with
        Pre  => Fst <= Lst,
        Post =>
          Length (All_From_Seq'Result) = To_Big (Lst - Fst)
          and then
            (for all I in Interval'(1, To_Big (Lst - Fst)) =>
               To_Big (Get (All_From_Seq'Result, I)) = To_Big (Lst) - I + 1);

      function LL_Free (S : Set) return Sequence
      is (if S.Free < 0
          then All_From_Seq (-S.Free - 1, S.Capacity)
          else LL_Sequence (S.Free, S.Nodes))
      with Pre => (if S.Free >= 0 then Is_Acyclic (S.Free, S.Nodes));

      --  Returns the position of node I in the linked list starting at Fst,
      --  or 0 if not present.
      function Find
        (M : Nodes_Type; Fst : Count_Type; I : Positive_Count_Type)
         return Big_Natural
      with
        Pre  =>
          Fst <= M'Last and then I <= M'Last and then Is_Acyclic (Fst, M),
        Post =>
          Find'Result <= Last (LL_Sequence (Fst, M))
          and then
            (if Find'Result > 0
             then Get (LL_Sequence (Fst, M), Find'Result) = I)
          and then
            (for all K in
               Interval'(Find'Result + 1, Last (LL_Sequence (Fst, M))) =>
               Get (LL_Sequence (Fst, M), K) /= I)
          and then (if Reachable (Fst, M, I) then Find'Result /= 0);

      --  Returns the position of the first node equivalent to E in the list
      --  starting at Fst.
      function Find
        (M : Nodes_Type; Fst : Count_Type; E : Element_Type) return Big_Natural
      with
        Pre  =>
          Fst <= M'Last
          and then Is_Acyclic (Fst, M)
          and then
            (for all I of Reachable_Set (Fst, M) => M (I).Element'Initialized),
        Post =>
          Find'Result <= Last (LL_Sequence (Fst, M))
          and then
            (if Find'Result > 0
             then
               Equivalent_Elements
                 (M (Get (LL_Sequence (Fst, M), Find'Result)).Element.V, E))
          and then
            (for all K in
               Interval'(Find'Result + 1, Last (LL_Sequence (Fst, M))) =>
               not Equivalent_Elements
                     (M (Get (LL_Sequence (Fst, M), K)).Element.V, E));

      --  Proves the linked list for bucket B has no duplicate node indexes
      procedure Lemma_LL_Sequence_No_Duplicated_Indexes
        (S : Set; B : Hash_Type)
      with
        Pre  => LL_Correct (S) and then B in 1 .. S.Modulus,
        Post => No_Duplicated_Indexes (LL_Sequence (S.Buckets (B), S.Nodes));
   end Private_Model;
   use Private_Model;

   package body Basic_Model is
      pragma Annotate (GNATprove, Unhide_Info, "Package_Body");

      ----------------------------
      -- First_Non_Empty_Bucket --
      ----------------------------

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

      ------------------------------------
      -- Lemma_LL_No_Duplicated_Indexes --
      ------------------------------------

      procedure Lemma_LL_No_Duplicated_Indexes (S : Set) is
      begin
         for B in S.Buckets'Range loop
            Lemma_LL_Sequence_No_Duplicated_Indexes (S, B);
            pragma
              Loop_Invariant
                (for all K in 1 .. B =>
                   No_Duplicated_Indexes
                     (LL_Sequence (S.Buckets (K), S.Nodes)));
         end loop;
      end Lemma_LL_No_Duplicated_Indexes;

      function LL_Buckets (S : Set) return Mem_Seq_Array
      is (for B in 1 .. S.Modulus => LL_Sequence (S.Buckets (B), S.Nodes))
      with Pre => LL_Correct (S);

      function LL_Correct (S : Set) return Boolean
      is (LL_Correct_Free_List (S)
          and then LL_Correct_Is_Acyclic_Buckets (S)
          and then LL_Correct_Buckets_Element (S));

      function LL_Invariant (S : Set) return Boolean
      is (LL_Correct (S)
          and then LL_Complete (S)
          and then LL_Has_Element (S)
          and then LL_Length (S));

      function LL_Model (S : Set) return Set_LL_Model
      is ((Capacity => S.Capacity,
           Modulus  => S.Modulus,
           Values   => Values_From_Nodes (S),
           Buckets  => LL_Buckets (S)));

      --------------------------------
      -- Prove_Invariant_On_Default --
      --------------------------------

      procedure Prove_Invariant_On_Default (S : Set) is
      begin
         if Default_Init (S) then
            for K in 1 .. S.Modulus loop
               pragma
                 Loop_Invariant (Num_Allocated (S.Buckets, S.Nodes, K) = 0);
               pragma
                 Loop_Invariant (Num_Allocated (LL_Model (S).Buckets, K) = 0);
            end loop;
         end if;
      end Prove_Invariant_On_Default;

   end Basic_Model;

   package body Private_Model is

      --  Subprogram bodies

      ------------------
      -- All_From_Seq --
      ------------------

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

      ---------------
      -- Empty_Seq --
      ---------------

      function Empty_Seq return Sequence is
      begin
         return S : Sequence do
            null;
         end return;
      end Empty_Seq;

      ----------
      -- Find --
      ----------

      function Find
        (M : Nodes_Type; Fst : Count_Type; I : Positive_Count_Type)
         return Big_Natural
      is
         C : Count_Type range 0 .. M'Last := Fst;
      begin
         Disclose_Recursive_Definitions;
         while C /= 0 loop
            pragma Loop_Invariant (Is_Acyclic (C, M));
            pragma Loop_Invariant (LL_Sequence (C, M) <= LL_Sequence (Fst, M));
            pragma
              Loop_Invariant (Reachable (C, M, I) = Reachable (Fst, M, I));
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
            C := M (C).Next;
         end loop;
         return 0;
      end Find;

      ----------
      -- Find --
      ----------

      function Find
        (M : Nodes_Type; Fst : Count_Type; E : Element_Type) return Big_Natural
      is
         C : Count_Type range 0 .. M'Last := Fst;
      begin
         Disclose_Recursive_Definitions;
         while C /= 0 loop
            pragma Loop_Invariant (Is_Acyclic (C, M));
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
                         (M (Get (LL_Sequence (Fst, M), K)).Element.V, E));
            pragma Loop_Variant (Decreases => Length (Reachable_Set (C, M)));
            if Equivalent_Elements (M (C).Element.V, E) then
               return Last (LL_Sequence (C, M));
            end if;
            C := M (C).Next;
         end loop;
         return 0;
      end Find;

      --  Proofs of lemmas

      --------------------------
      -- Lemma_Length_Complete --
      --------------------------

      procedure Lemma_Length_Complete (S : Set) is

         function All_Set (Capacity : Count_Type) return Memory_Index_Set
         with
           Post =>
             Length (All_Set'Result) = To_Big (Capacity)
             and then
               (for all I in 1 .. Capacity => Contains (All_Set'Result, I))
             and then (for all E of All_Set'Result => E <= Capacity);

         function All_Set (Capacity : Count_Type) return Memory_Index_Set is
         begin
            return S : Memory_Index_Set do
               for I in 1 .. Capacity loop
                  S := Add (S, I);
                  pragma Loop_Invariant (Length (S) = To_Big (I));
                  pragma
                    Loop_Invariant (for all K in 1 .. I => Contains (S, K));
                  pragma Loop_Invariant (for all K of S => K in 1 .. I);
               end loop;
            end return;
         end All_Set;

         Free_Cells      : Memory_Index_Set;
         Allocated_Cells : Memory_Index_Set;

      begin
         --  Construct the set of free nodes

         if S.Free >= 0 then
            Free_Cells := Reachable_Set (S.Free, S.Nodes);
         else
            for I in -S.Free .. S.Capacity loop
               Free_Cells := Add (Free_Cells, I);
               pragma
                 Loop_Invariant
                   (Length (Free_Cells) = To_Big (I + S.Free + 1));
               pragma
                 Loop_Invariant
                   (for all K in -S.Free .. I => Contains (Free_Cells, K));
               pragma
                 Loop_Invariant (for all K of Free_Cells => K in -S.Free .. I);
            end loop;
         end if;
         pragma
           Assert
             (for all I in S.Nodes'Range =>
                Is_Free (S.Free, S.Nodes, I) = Contains (Free_Cells, I));

         --  Construct the set of allocated nodes

         for B in S.Buckets'Range loop
            pragma
              Assert
                (No_Overlap
                   (Allocated_Cells, Reachable_Set (S.Buckets (B), S.Nodes)));
            Allocated_Cells :=
              Union (Allocated_Cells, Reachable_Set (S.Buckets (B), S.Nodes));
            pragma
              Loop_Invariant
                (for all I of Allocated_Cells =>
                   (for some K in 1 .. B =>
                      Contains (Reachable_Set (S.Buckets (K), S.Nodes), I)));
            pragma
              Loop_Invariant
                (for all K in 1 .. B =>
                   Reachable_Set (S.Buckets (K), S.Nodes) <= Allocated_Cells);
            pragma
              Loop_Invariant
                (Length (Allocated_Cells)
                 = Num_Allocated (S.Buckets, S.Nodes, B));
            pragma
              Loop_Invariant
                (Is_Empty (Intersection (Allocated_Cells, Free_Cells)));
         end loop;
         pragma
           Assert
             (for all I in S.Nodes'Range =>
                Is_Allocated (S.Buckets, S.Nodes, I)
                = Contains (Allocated_Cells, I));

         pragma Assert (Num_Overlaps (Allocated_Cells, Free_Cells) = 0);
         pragma
           Assert
             (Num_Overlaps
                (Union (Allocated_Cells, Free_Cells), All_Set (S.Capacity))
              = To_Big (S.Capacity));
      end Lemma_Length_Complete;

      ---------------------------------------------
      -- Lemma_LL_Sequence_No_Duplicated_Indexes --
      ---------------------------------------------

      procedure Lemma_LL_Sequence_No_Duplicated_Indexes
        (S : Set; B : Hash_Type)
      is
         C : Count_Type range 0 .. S.Capacity := S.Buckets (B);
      begin
         while C /= 0 loop
            Lemma_Is_Acyclic_Def (C, S.Nodes);
            Lemma_Reachable_Def (C, S.Nodes);
            Lemma_LL_Sequence_Def (C, S.Nodes);
            C := S.Nodes (C).Next;

            pragma
              Loop_Variant (Decreases => Length (Reachable_Set (C, S.Nodes)));
            pragma Loop_Invariant (Is_Acyclic (C, S.Nodes));
            pragma
              Loop_Invariant
                (LL_Sequence (C, S.Nodes)
                 <= LL_Sequence (S.Buckets (B), S.Nodes));
            pragma
              Loop_Invariant
                (for all P1 in
                   Interval'
                     (Length (LL_Sequence (C, S.Nodes)) + 1,
                      Length (LL_Sequence (S.Buckets (B), S.Nodes))) =>
                   (for all P2 in Interval'(1, P1 - 1) =>
                      Get (LL_Sequence (S.Buckets (B), S.Nodes), P1)
                      /= Get (LL_Sequence (S.Buckets (B), S.Nodes), P2)));
         end loop;
      end Lemma_LL_Sequence_No_Duplicated_Indexes;

      --------------------------
      -- Lemma_Values_Buckets --
      --------------------------

      procedure Lemma_Values_Buckets
        (S : Set; B : Positive_Hash_Type; I : Positive_Count_Type)
      is null;

      ----------------------------
      -- Lemma_Values_Preserved --
      ----------------------------

      procedure Lemma_Values_Preserved (S1, S2 : Set; I : Count_Type := 0)
      is null;

      -----------------------
      -- Values_From_Nodes --
      -----------------------

      function Values_From_Nodes (S : Set) return Values_Type is
         C : Count_Type range 0 .. S.Capacity;
      begin
         return M : Values_Type do
            for B in 1 .. S.Modulus loop
               C := S.Buckets (B);
               while C > 0 loop
                  pragma Loop_Invariant (Is_Acyclic (C, S.Nodes));
                  pragma
                    Loop_Invariant
                      (Reachable_Set (C, S.Nodes)
                       <= Reachable_Set (S.Buckets (B), S.Nodes));
                  pragma
                    Loop_Invariant
                      (for all I of M =>
                         Find_Bucket (Get (M, I), S.Modulus) <= B);
                  pragma
                    Loop_Invariant
                      (for all I of M => not Reachable (C, S.Nodes, I));
                  pragma
                    Loop_Invariant
                      (for all I of M =>
                         Reachable
                           (S.Buckets (Find_Bucket (Get (M, I), S.Modulus)),
                            S.Nodes,
                            I));
                  pragma
                    Loop_Invariant
                      (for all B2 in S.Buckets'First .. B - 1 =>
                         (for all I of
                            Reachable_Set (S.Buckets (B2), S.Nodes) =>
                            Has_Key (M, I)));
                  pragma
                    Loop_Invariant
                      (for all I of Reachable_Set (S.Buckets (B), S.Nodes) =>
                         Reachable (C, S.Nodes, I) or Has_Key (M, I));
                  pragma
                    Loop_Invariant
                      (for all I of M =>
                         S.Nodes (I).Element'Initialized
                         and then S.Nodes (I).Element.V = Get (M, I));
                  pragma
                    Loop_Variant
                      (Decreases => Length (Reachable_Set (C, S.Nodes)));
                  M := Add (M, C, S.Nodes (C).Element.V);
                  Lemma_Is_Acyclic_Def (C, S.Nodes);
                  Lemma_Reachable_Def (C, S.Nodes);
                  C := S.Nodes (C).Next;
               end loop;
               pragma
                 Assert
                   (for all I of Reachable_Set (S.Buckets (B), S.Nodes) =>
                      Has_Key (M, I));
               pragma
                 Loop_Invariant
                   (for all I of M =>
                      Find_Bucket (Get (M, I), S.Modulus) <= B);
               pragma
                 Loop_Invariant
                   (for all I of M =>
                      Reachable
                        (S.Buckets (Find_Bucket (Get (M, I), S.Modulus)),
                         S.Nodes,
                         I));
               pragma
                 Loop_Invariant
                   (for all B2 in 1 .. B =>
                      (for all I of Reachable_Set (S.Buckets (B2), S.Nodes) =>
                         Has_Key (M, I)));
               pragma
                 Loop_Invariant
                   (for all I of M =>
                      S.Nodes (I).Element'Initialized
                      and then S.Nodes (I).Element.V = Get (M, I));
            end loop;
         end return;
      end Values_From_Nodes;

   end Private_Model;

   use Private_Model.Memory_Index_Sets;
   use Private_Model.Node_Reachability;

   pragma Unevaluated_Use_Of_Old (Allow);

   --  Returns the default hash modulus (a suitable prime) for a set of the
   --  given Capacity.
   function Default_Modulus (C : Count_Type) return Positive_Hash_Type;

   function To_Prime (Length : Count_Type) return Positive_Hash_Type;
   --  Returns the smallest Element in Primes not less than Length

   --  Removes a node from the free list and returns its index in I
   procedure Allocate (S : in out Set; I : out Positive_Count_Type)
   with
     Pre  => LL_Invariant (S) and then Num_Allocated (S) < To_Big (S.Capacity),
     Post =>
       I = Get (LL_Free (S)'Old, Last (LL_Free (S))'Old)
       and then I <= S.Capacity
       and then LL_Correct (S)
       and then LL_Length (S)
       and then LL_Has_Element (S)
       and then
         (for all K in 1 .. S.Capacity =>
            (if K /= I
             then
               Is_Free (S.Free, S.Nodes, K)
               or else Is_Allocated (S.Buckets, S.Nodes, K)))
       and then S.Length = S.Length'Old
       and then not Is_Free (S.Free, S.Nodes, I)
       and then (for all B of S.Buckets => not Reachable (B, S.Nodes, I))
       and then LL_Model (S).Values = LL_Model (S).Values'Old
       and then LL_Model (S).Buckets = LL_Model (S).Buckets'Old
       and then
         Is_Remove (LL_Free (S)'Old, Last (LL_Free (S)'Old), LL_Free (S));

   --  Returns node I to the free list (node must not be linked into any bucket)
   procedure Deallocate (S : in out Set; I : Positive_Count_Type)
   with
     Pre  =>
       LL_Correct (S)
       and then LL_Length (S)
       and then LL_Has_Element (S)
       and then I <= S.Capacity
       and then
         (for all K in 1 .. S.Capacity =>
            (if K /= I
             then
               Is_Free (S.Free, S.Nodes, K)
               or else Is_Allocated (S.Buckets, S.Nodes, K)))
       and then not Is_Free (S.Free, S.Nodes, I)
       and then (for all B of S.Buckets => not Reachable (B, S.Nodes, I)),
     Post =>
       LL_Invariant (S)
       and then S.Length = S.Length'Old
       and then LL_Model (S).Values'Old = LL_Model (S).Values
       and then LL_Model (S).Buckets = LL_Model (S).Buckets'Old
       and then Is_Add (LL_Free (S)'Old, I, LL_Free (S));

   --  Links allocated node I (containing element E) into its hash bucket
   --  and increments the length.
   procedure Insert_Internal
     (S : in out Set; I : Positive_Count_Type; E : Element_Type)
   with
     Pre  =>
       LL_Correct (S)
       and then LL_Length (S)
       and then LL_Has_Element (S)
       and then S.Length < S.Capacity
       and then I <= S.Capacity
       and then
         (for all K in 1 .. S.Capacity =>
            (if K /= I
             then
               Is_Free (S.Free, S.Nodes, K)
               or else Is_Allocated (S.Buckets, S.Nodes, K)))
       and then not Is_Free (S.Free, S.Nodes, I)
       and then (for all K of S.Buckets => not Reachable (K, S.Nodes, I)),
     Post =>
       LL_Correct (S)
       and then LL_Length (S)
       and then LL_Complete (S)
       and then LL_Has_Element (S)
       and then S.Length = S.Length'Old + 1
       and then LL_Free (S) = LL_Free (S)'Old
       and then
         Is_Add
           (LL_Model (S).Buckets (Find_Bucket (E, S.Modulus))'Old,
            I,
            LL_Model (S).Buckets (Find_Bucket (E, S.Modulus)))
       and then
         (for all K in 1 .. S.Modulus =>
            (if Find_Bucket (E, S.Modulus) /= K
             then LL_Model (S).Buckets (K) = LL_Model (S).Buckets'Old (K)))
       and then LL_Model (S).Values'Old <= LL_Model (S).Values
       and then
         Keys_Included_Except (LL_Model (S).Values, LL_Model (S).Values'Old, I)
       and then Get (LL_Model (S).Values, I) = E;

   --  Unlinks node I from its hash bucket without returning it to the free list
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
       and then
         (for all K in 1 .. S.Capacity =>
            (if K /= I
             then
               Is_Free (S.Free, S.Nodes, K)
               or else Is_Allocated (S.Buckets, S.Nodes, K)))
       and then not Is_Free (S.Free, S.Nodes, I)
       and then (for all B of S.Buckets => not Reachable (B, S.Nodes, I))
       and then S.Length = S.Length'Old - 1
       and then LL_Free (S) = LL_Free (S)'Old
       and then
         Is_Remove
           (LL_Model (S).Buckets
              (Find_Bucket (S.Nodes (I).Element.V, S.Modulus))'Old,
            Internal_Models.Find
              (LL_Model (S).Buckets
                 (Find_Bucket (S.Nodes (I).Element.V, S.Modulus)),
               I)'Old,
            LL_Model (S).Buckets
              (Find_Bucket (S.Nodes (I).Element.V, S.Modulus)'Old))
       and then
         (for all K in 1 .. S.Modulus =>
            (if Find_Bucket (S.Nodes (I).Element.V, S.Modulus) /= K
             then LL_Model (S).Buckets (K) = LL_Model (S).Buckets'Old (K)))
       and then LL_Model (S).Values <= LL_Model (S).Values'Old
       and then
         Keys_Included_Except
           (LL_Model (S).Values'Old, LL_Model (S).Values, I);

   --  Finds and unlinks the node equivalent to E without returning it to
   --  the free list; returns its index.
   procedure Delete_Key_No_Free
     (S : in out Set; E : Element_Type; I : out Count_Type)
   with
     Pre  =>
       LL_Correct (S)
       and then LL_Complete (S)
       and then LL_Length (S)
       and then LL_Has_Element (S),
     Post =>
       (if Internal_Models.Find
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
          and then
            I
            = Get
                (LL_Model (S).Buckets (Find_Bucket (E, S.Modulus))'Old,
                 Internal_Models.Find
                   (LL_Model (S).Buckets (Find_Bucket (E, S.Modulus)),
                    LL_Model (S).Values,
                    E)'Old)
          and then I <= S.Capacity
          and then
            (for all K in 1 .. S.Capacity =>
               (if K /= I
                then
                  Is_Free (S.Free, S.Nodes, K)
                  or else Is_Allocated (S.Buckets, S.Nodes, K)))
          and then not Is_Free (S.Free, S.Nodes, I)
          and then (for all B of S.Buckets => not Reachable (B, S.Nodes, I))
          and then
            Is_Remove
              (LL_Model (S).Buckets (Find_Bucket (E, S.Modulus))'Old,
               Find
                 (LL_Model (S).Buckets (Find_Bucket (E, S.Modulus)),
                  LL_Model (S).Values,
                  E)'Old,
               LL_Model (S).Buckets (Find_Bucket (E, S.Modulus)))
          and then S.Length = S.Length'Old - 1
          and then LL_Free (S) = LL_Free (S)'Old
          and then
            (for all K in 1 .. S.Modulus =>
               (if Find_Bucket (E, S.Modulus) /= K
                then LL_Model (S).Buckets (K) = LL_Model (S).Buckets'Old (K)))
          and then LL_Model (S).Values <= LL_Model (S).Values'Old
          and then
            Keys_Included_Except
              (LL_Model (S).Values'Old, LL_Model (S).Values, I));

   --  Updates the element at node I to E; bucket assignment must remain
   --  unchanged.
   procedure Replace_Internal
     (S : in out Set; I : Positive_Count_Type; E : Element_Type)
   with
     Pre  =>
       LL_Invariant (S)
       and then Has_Element (S, I)
       and then
         Find_Bucket (Get (LL_Model (S).Values, I), S.Modulus)
         = Find_Bucket (E, S.Modulus),
     Post =>
       LL_Invariant (S)
       and then Get (LL_Model (S).Values, I) = E
       and then LL_Model (S).Buckets = LL_Model (S).Buckets'Old
       and then Same_Keys (LL_Model (S).Values'Old, LL_Model (S).Values)
       and then
         Elements_Equal_Except
           (LL_Model (S).Values'Old, LL_Model (S).Values, I);

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

   --------------
   -- Allocate --
   --------------

   procedure Allocate (S : in out Set; I : out Positive_Count_Type) is
      Old_S     : constant Set := S
      with Ghost;
      Old_Free  : constant Count_Type'Base := S.Free
      with Ghost;
      Old_Nodes : constant Nodes_Type := S.Nodes
      with Ghost;

      procedure Prove_Invariant
      with
        Ghost
        --  Reestablish the invariant
      is
      begin
         --  The tail of the free list is preserved

         if Old_Free >= 0 then
            Lemma_Is_Acyclic_Def (Old_Free, Old_Nodes);
            Lemma_Reachable_Def (Old_Free, Old_Nodes);
            Lemma_LL_Sequence_Def (Old_Free, Old_Nodes);
            Lemma_Is_Acyclic_Preserved (S.Free, Old_Nodes, S.Nodes);
            Lemma_Reachable_Preserved (S.Free, Old_Nodes, S.Nodes);
            Lemma_LL_Sequence_Preserved (S.Free, Old_Nodes, S.Nodes);
            pragma
              Assert
                (Is_Remove
                   (LL_Sequence (Old_Free, Old_Nodes),
                    Last (LL_Sequence (Old_Free, Old_Nodes)),
                    LL_Sequence (S.Free, S.Nodes)));
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
         S.Free := S.Nodes (S.Free).Next;
      end if;

      Prove_Invariant;
      Lemma_Values_Preserved (Old_S, S);
   end Allocate;

   ------------------------
   -- Conditional_Insert --
   ------------------------

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
         pragma Loop_Invariant (Is_Acyclic (I, S.Nodes));
         pragma
           Loop_Invariant
             (LL_Sequence (I, S.Nodes)
              <= LL_Sequence (S.Buckets (B), S.Nodes));
         pragma
           Loop_Invariant
             (for all K in
                Interval'
                  (Last (LL_Sequence (I, S.Nodes)) + 1,
                   Last (LL_Sequence (S.Buckets (B), S.Nodes))) =>
                not Equivalent_Elements
                      (S.Nodes (Get (LL_Sequence (S.Buckets (B), S.Nodes), K))
                         .Element
                         .V,
                       E));
         pragma
           Loop_Variant (Decreases => Length (Reachable_Set (I, S.Nodes)));
         if Equivalent_Elements (S.Nodes (I).Element.V, E) then
            pragma Assert (Find (S.Nodes, S.Buckets (B), E) /= 0);
            Inserted := False;
            return;
         end if;
         Lemma_Is_Acyclic_Def (I, S.Nodes);
         Lemma_Reachable_Def (I, S.Nodes);
         Lemma_LL_Sequence_Def (I, S.Nodes);
         I := S.Nodes (I).Next;
      end loop;
      pragma
        Assert
          (for all K in
             Interval'(1, Last (LL_Sequence (S.Buckets (B), S.Nodes))) =>
             not Equivalent_Elements
                   (S.Nodes (Get (LL_Sequence (S.Buckets (B), S.Nodes), K))
                      .Element
                      .V,
                    E));
      pragma Assert (Find (S.Nodes, S.Buckets (B), E) = 0);

      Inserted := True;
      Allocate (S, I);
      Insert_Internal (S, I, E);
   end Conditional_Insert;

   --------------
   -- Contains --
   --------------

   function Contains (S : Set; E : Element_Type) return Boolean is
   begin
      return Find (S, E) /= 0;
   end Contains;

   ----------------
   -- Deallocate --
   ----------------

   procedure Deallocate (S : in out Set; I : Positive_Count_Type) is
      Old_S : constant Set := S
      with Ghost;

      procedure Prove_Expand_Free_List (S, Old_S : Set)
      with
        --  Prove that we have preserved the free list after an expansion
        Ghost,
        Pre  =>
          S.Capacity > 0
          and then Old_S.Free < 0
          and then S.Nodes (S.Capacity).Next = 0
          and then S.Free = I
          and then Old_S.Free >= -S.Capacity
          and then I < -Old_S.Free
          and then S.Nodes (S.Free).Next = -Old_S.Free
          and then
            (for all L in -Old_S.Free .. S.Capacity - 1 =>
               S.Nodes (L).Next = L + 1),
        Post =>
          Is_Acyclic (S.Free, S.Nodes)
          and then
            Is_Add
              (All_From_Seq (-Old_S.Free - 1, S.Capacity),
               I,
               LL_Sequence (S.Free, S.Nodes))
          and then
            (for all L of Reachable_Set (S.Free, S.Nodes) =>
               L in -Old_S.Free .. S.Capacity or else L = I)
          and then
            (for all L in -Old_S.Free .. S.Capacity =>
               Reachable (S.Free, S.Nodes, L))
          and then (Reachable (S.Free, S.Nodes, I))
          and then
            (Length (Reachable_Set (S.Free, S.Nodes))
             = To_Big (S.Capacity + Old_S.Free + 2))
      is
      begin
         --  The tail of the free list is the extenion of the old free list

         for K in reverse -Old_S.Free .. S.Capacity loop
            Lemma_Is_Acyclic_Def (K, S.Nodes);
            Lemma_Reachable_Def (K, S.Nodes);
            Lemma_LL_Sequence_Def (K, S.Nodes);
            pragma Loop_Invariant (Is_Acyclic (K, S.Nodes));
            pragma
              Loop_Invariant
                (for all L of Reachable_Set (K, S.Nodes) =>
                   L in K .. S.Capacity);
            pragma
              Loop_Invariant
                (for all L in K .. S.Capacity => Reachable (K, S.Nodes, L));
            pragma
              Loop_Invariant
                (Length (Reachable_Set (K, S.Nodes))
                 = To_Big (S.Capacity - K + 1));
            pragma
              Loop_Invariant
                (Length (LL_Sequence (K, S.Nodes))
                 = To_Big (S.Capacity - K + 1));
            pragma
              Loop_Invariant
                (for all L in 1 .. Positive_Count_Type (S.Capacity - K + 1) =>
                   Get (LL_Sequence (K, S.Nodes), To_Big (L))
                   = S.Capacity - L + 1);
         end loop;
         pragma
           Assert
             (for all L in
                1 .. Positive_Count_Type (S.Capacity + Old_S.Free + 1) =>
                Get (LL_Sequence (-Old_S.Free, S.Nodes), To_Big (L))
                = Get
                    (All_From_Seq (-Old_S.Free - 1, S.Capacity), To_Big (L)));
         pragma
           Assert
             (LL_Sequence (-Old_S.Free, S.Nodes)
              = All_From_Seq (-Old_S.Free - 1, S.Capacity));

         --  I was added on top

         pragma Assert (S.Free = I and S.Nodes (S.Free).Next = -Old_S.Free);
         Lemma_Is_Acyclic_Def (S.Free, S.Nodes);
         Lemma_Reachable_Def (S.Free, S.Nodes);
         Lemma_LL_Sequence_Def (S.Free, S.Nodes);
      end Prove_Expand_Free_List;

      procedure Prove_Invariant (S, Old_S : Set)
      with
        Ghost,
        --  Reestablish the invariant
        Pre  =>
          LL_Correct (Old_S)
          and then LL_Length (Old_S)
          and then LL_Has_Element (Old_S)
          and then Old_S.Capacity = S.Capacity
          and then Old_S.Modulus = S.Modulus
          and then Old_S.Length = S.Length
          and then Old_S.Buckets = S.Buckets
          and then I <= S.Capacity
          and then not Is_Free (Old_S.Free, Old_S.Nodes, I)
          and then
            (for all K in 1 .. S.Capacity =>
               (if K /= I
                then
                  Is_Free (Old_S.Free, Old_S.Nodes, K)
                  or else Is_Allocated (Old_S.Buckets, Old_S.Nodes, K)))
          and then
            (for all B in Old_S.Buckets'Range =>
               (for all K of Reachable_Set (Old_S.Buckets (B), Old_S.Nodes) =>
                  Node_Preserved (Old_S.Nodes (K), S.Nodes (K))))
          and then
            (for all K in 1 .. S.Capacity =>
               (if Is_Free (Old_S.Free, Old_S.Nodes, K)
                then Old_S.Nodes (K).Has_Element = S.Nodes (K).Has_Element))
          and then not S.Nodes (I).Has_Element
          and then (if S.Free >= 0 then Is_Acyclic (S.Free, S.Nodes))
          and then
            (if Old_S.Free >= 0
             then
               S.Free >= 0
               and then
                 Reachable_Set (S.Free, S.Nodes)
                 = Add (Reachable_Set (Old_S.Free, Old_S.Nodes), I)
             elsif I + 1 = -Old_S.Free
             then S.Free = Old_S.Free + 1
             else
               S.Free >= 0
               and then
                 (for all K in 1 .. S.Capacity =>
                    Reachable (S.Free, S.Nodes, K)
                    = (K = I or K >= -Old_S.Free))),
        Post =>
          LL_Invariant (S)
          and then LL_Model (S).Values = LL_Model (Old_S).Values
          and then LL_Model (S).Buckets = LL_Model (Old_S).Buckets
      is
      begin
         --  Go through the bucket list to prove that their LL_Sequence is
         --  preserved.

         for B in 1 .. S.Modulus loop
            Lemma_Is_Acyclic_Preserved (S.Buckets (B), Old_S.Nodes, S.Nodes);
            Lemma_Reachable_Preserved (S.Buckets (B), Old_S.Nodes, S.Nodes);
            Lemma_LL_Sequence_Preserved (S.Buckets (B), Old_S.Nodes, S.Nodes);
            pragma
              Loop_Invariant
                (Num_Allocated (S.Buckets, S.Nodes, B)
                 = Num_Allocated (Old_S.Buckets, Old_S.Nodes, B));
            pragma
              Loop_Invariant
                (for all I in 1 .. B => Is_Acyclic (S.Buckets (I), S.Nodes));
            pragma
              Loop_Invariant
                (for all I in 1 .. B =>
                   Reachable_Set (S.Buckets (I), S.Nodes)
                   = Reachable_Set (Old_S.Buckets (I), Old_S.Nodes));
            pragma
              Loop_Invariant
                (for all I in 1 .. B =>
                   LL_Sequence (S.Buckets (I), S.Nodes)
                   = LL_Sequence (Old_S.Buckets (I), Old_S.Nodes));
            pragma
              Loop_Invariant
                (for all I in 1 .. B =>
                   Length (Reachable_Set (S.Buckets (I), S.Nodes))
                   = Length (Reachable_Set (Old_S.Buckets (I), Old_S.Nodes)));
         end loop;

         pragma
           Assert
             (By
                (LL_Invariant (S),
                 --  Prove LL_Correct by case analysis
                 (if Old_S.Free >= 0 then LL_Correct (S))
                 and
                   (if Old_S.Free < 0 and then I + 1 = -Old_S.Free
                    then LL_Correct (S))
                 and
                   (if Old_S.Free < 0 and then I + 1 /= -Old_S.Free
                    then LL_Correct (S))));
         Lemma_Values_Preserved (Old_S, S);
      end Prove_Invariant;

   begin
      if S.Free >= 0 then
         S.Nodes (I).Next := S.Free;
         S.Free := I;

         --  I has been added on top of the old free list

         Lemma_Is_Acyclic_Preserved (Old_S.Free, Old_S.Nodes, S.Nodes);
         Lemma_Reachable_Preserved (Old_S.Free, Old_S.Nodes, S.Nodes);
         Lemma_LL_Sequence_Preserved (Old_S.Free, Old_S.Nodes, S.Nodes);
         Lemma_Is_Acyclic_Def (S.Free, S.Nodes);
         Lemma_Reachable_Def (S.Free, S.Nodes);
         Lemma_LL_Sequence_Def (S.Free, S.Nodes);
         pragma Assert (Is_Acyclic (S.Free, S.Nodes));
         pragma
           Assert
             (Reachable_Set (S.Free, S.Nodes)
              = Add (Reachable_Set (Old_S.Free, Old_S.Nodes), I));
         pragma
           Assert
             (Is_Add
                (LL_Sequence (Old_S.Free, Old_S.Nodes),
                 I,
                 LL_Sequence (S.Free, S.Nodes)));
      elsif I + 1 = -S.Free then
         S.Free := S.Free + 1;
      else
         S.Nodes (S.Capacity).Next := 0;
         for K in -S.Free .. S.Capacity - 1 loop
            S.Nodes (K).Next := K + 1;
            pragma
              Loop_Invariant
                (for all L in -S.Free .. K => S.Nodes (L).Next = L + 1);
         end loop;
         S.Nodes (I).Next := -S.Free;
         S.Free := I;
         Prove_Expand_Free_List (S, Old_S);
      end if;
      Prove_Invariant (S, Old_S);
   end Deallocate;

   ---------------------
   -- Default_Modulus --
   ---------------------

   function Default_Modulus (C : Count_Type) return Positive_Hash_Type is
   begin
      return To_Prime (C);
   end Default_Modulus;

   ------------
   -- Delete --
   ------------

   procedure Delete (S : in out Set; I : Positive_Count_Type) is
      B          : constant Hash_Type :=
        Find_Bucket (S.Nodes (I).Element.V, S.Modulus)
      with Ghost;
      Old_Bucket : constant Sequence := LL_Model (S).Buckets (B)
      with Ghost;
   begin
      Delete_No_Free (S, I);
      Deallocate (S, I);
   end Delete;

   ----------------
   -- Delete_Key --
   ----------------

   procedure Delete_Key (S : in out Set; E : Element_Type) is
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

   ------------------------
   -- Delete_Key_No_Free --
   ------------------------

   procedure Delete_Key_No_Free
     (S : in out Set; E : Element_Type; I : out Count_Type)
   is
      B     : constant Hash_Type := Find_Bucket (E, S.Modulus);
      Old_S : constant Set := S
      with Ghost;
      Pos   : constant Big_Natural := Find (S.Nodes, S.Buckets (B), E)
      with Ghost;
      pragma
        Assert
          (Pos
           = Internal_Models.Find
               (LL_Model (S).Buckets (Find_Bucket (E, S.Modulus)),
                LL_Model (S).Values,
                E));

      procedure Prove_Invariant (S, Old_S : Set)
      with
        --  Reestablish the invariant
        Ghost,
        Pre  =>
          LL_Correct (Old_S)
          and then LL_Complete (Old_S)
          and then LL_Has_Element (Old_S)
          and then Old_S.Capacity = S.Capacity
          and then Old_S.Modulus = S.Modulus
          and then S.Free = Old_S.Free
          and then B = Find_Bucket (E, S.Modulus)
          and then I in 1 .. S.Capacity
          and then Pos = Find (Old_S.Nodes, Old_S.Buckets (B), E)
          and then Pos > 0
          and then
            (for all K in 1 .. S.Modulus =>
               (if K /= B then Old_S.Buckets (K) = S.Buckets (K)))
          and then Reachable (Old_S.Buckets (B), Old_S.Nodes, I)
          and then
            (for all I in 1 .. S.Capacity =>
               (if not Reachable (Old_S.Buckets (B), Old_S.Nodes, I)
                then Node_Preserved (S.Nodes (I), Old_S.Nodes (I))))
          and then
            (for all I of Reachable_Set (Old_S.Buckets (B), Old_S.Nodes) =>
               Node_Preserved
                 (S.Nodes (I),
                  (Old_S.Nodes (I)
                   with delta
                     Next        => S.Nodes (I).Next,
                     Has_Element => S.Nodes (I).Has_Element)))
          and then Is_Acyclic (S.Buckets (B), S.Nodes)
          and then
            Reachable_Set (S.Buckets (B), S.Nodes)
            = Remove (Reachable_Set (Old_S.Buckets (B), Old_S.Nodes), I)
          and then
            (for all I of Reachable_Set (S.Buckets (B), S.Nodes) =>
               S.Nodes (I).Has_Element)
          and then not S.Nodes (I).Has_Element
          and then
            Is_Remove
              (LL_Sequence (Old_S.Buckets (B), Old_S.Nodes),
               Pos,
               LL_Sequence (S.Buckets (B), S.Nodes)),
        Post =>
          LL_Correct (S)
          and then LL_Has_Element (S)
          and then not Is_Free (S.Free, S.Nodes, I)
          and then LL_Free (S) = LL_Free (Old_S)
          and then
            (for all K in 1 .. S.Modulus =>
               (if K /= B
                then
                  LL_Sequence (Old_S.Buckets (K), Old_S.Nodes)
                  = LL_Sequence (S.Buckets (K), S.Nodes)))
          and then
            (for all K in 1 .. S.Capacity =>
               (if K /= I
                then
                  Is_Free (S.Free, S.Nodes, K)
                  or else Is_Allocated (S.Buckets, S.Nodes, K)))
          and then
            Num_Allocated (S.Buckets, S.Nodes, S.Modulus)
            = Num_Allocated (Old_S.Buckets, Old_S.Nodes, S.Modulus) - 1
          and then LL_Model (S).Values <= LL_Model (Old_S).Values
          and then
            Keys_Included_Except
              (LL_Model (Old_S).Values, LL_Model (S).Values, I)
      is
      begin
         --  Go through the bucket list to prove that other buckets are
         --  preserved.

         for K in 1 .. S.Modulus loop
            if K /= B then
               Lemma_Is_Acyclic_Preserved
                 (S.Buckets (K), Old_S.Nodes, S.Nodes);
               Lemma_Reachable_Preserved (S.Buckets (K), Old_S.Nodes, S.Nodes);
               Lemma_LL_Sequence_Preserved
                 (S.Buckets (K), Old_S.Nodes, S.Nodes);
            end if;
            pragma
              Loop_Invariant
                (if K < B
                 then
                   Num_Allocated (S.Buckets, S.Nodes, K)
                   = Num_Allocated (Old_S.Buckets, Old_S.Nodes, K)
                 else
                   Num_Allocated (S.Buckets, S.Nodes, K)
                   = Num_Allocated (Old_S.Buckets, Old_S.Nodes, K) - 1);
            pragma
              Loop_Invariant
                (for all I in 1 .. K => Is_Acyclic (S.Buckets (I), S.Nodes));
            pragma
              Loop_Invariant
                (for all I in 1 .. K =>
                   (if I /= B
                    then
                      Reachable_Set (Old_S.Buckets (I), Old_S.Nodes)
                      = Reachable_Set (S.Buckets (I), S.Nodes)));
            pragma
              Loop_Invariant
                (for all I in 1 .. K =>
                   (if I /= B
                    then
                      LL_Sequence (Old_S.Buckets (I), Old_S.Nodes)
                      = LL_Sequence (S.Buckets (I), S.Nodes)));
            pragma
              Loop_Invariant
                (for all I in 1 .. K =>
                   (if I /= B
                    then
                      Length (Reachable_Set (S.Buckets (I), S.Nodes))
                      = Length
                          (Reachable_Set (Old_S.Buckets (I), Old_S.Nodes))));
         end loop;

         --  The free list is preserved

         if S.Free >= 0 then
            Lemma_Is_Acyclic_Preserved (S.Free, Old_S.Nodes, S.Nodes);
            Lemma_Reachable_Preserved (S.Free, Old_S.Nodes, S.Nodes);
            Lemma_LL_Sequence_Preserved (S.Free, Old_S.Nodes, S.Nodes);
            pragma
              Assert
                (Reachable_Set (S.Free, S.Nodes)
                 = Reachable_Set (Old_S.Free, Old_S.Nodes));
         end if;

         pragma Assert (LL_Correct (S));
         pragma
           Assert
             (for all K in 1 .. S.Capacity =>
                (if K /= I
                 then
                   Is_Allocated (S.Buckets, S.Nodes, K)
                   = Is_Allocated (Old_S.Buckets, Old_S.Nodes, K)));
         Lemma_Values_Preserved (Old_S, S, I);
         Lemma_Values_Buckets (Old_S, B, I);
         Lemma_Values_Buckets (S, B, I);
      end Prove_Invariant;

      procedure Prove_Length (S : Set)
      with
        Ghost,
        Pre  =>
          B in 1 .. S.Modulus and then LL_Correct (S) and then LL_Length (S),
        Post => (if Find (S.Nodes, S.Buckets (B), E) /= 0 then S.Length > 0)
      is
      begin
         for K in B .. S.Modulus loop
            pragma
              Loop_Invariant
                (if Find (S.Nodes, S.Buckets (B), E) /= 0
                 then Num_Allocated (S.Buckets, S.Nodes, K) > 0);
         end loop;
      end Prove_Length;

   begin

      --  Show that there is at least an allocated cell if E is in the set

      Prove_Length (S);

      I := S.Buckets (B);

      if I = 0 then
         pragma Assert (Pos = 0);
         return;
      end if;

      if Equivalent_Elements (S.Nodes (S.Buckets (B)).Element.V, E) then
         Lemma_Is_Acyclic_Def (I, S.Nodes);
         Lemma_Reachable_Def (I, S.Nodes);
         Lemma_LL_Sequence_Def (I, S.Nodes);

         S.Buckets (B) := S.Nodes (I).Next;
         S.Nodes (I).Has_Element := False;

         --  I has been removed from S.Buckets (B)

         Lemma_Is_Acyclic_Preserved (S.Buckets (B), Old_S.Nodes, S.Nodes);
         Lemma_Reachable_Preserved (S.Buckets (B), Old_S.Nodes, S.Nodes);
         Lemma_LL_Sequence_Preserved (S.Buckets (B), Old_S.Nodes, S.Nodes);
         pragma Assert (Is_Acyclic (S.Buckets (B), S.Nodes));
         pragma
           Assert
             (Reachable_Set (S.Buckets (B), S.Nodes)
              = Remove (Reachable_Set (I, Old_S.Nodes), I));
         pragma
           Assert
             (Is_Remove
                (LL_Sequence (I, Old_S.Nodes),
                 Find (Old_S.Nodes, I, I),
                 LL_Sequence (S.Buckets (B), S.Nodes)));
      else
         declare
            Capacity : constant Count_Type := S.Capacity;
            P        : Positive_Count_Type range 1 .. Capacity;
         begin
            loop

               --  We are traversing the list rooted at S.Buckets (B) in
               --  S.Nodes.

               pragma Loop_Invariant (I /= 0 and I <= S.Capacity);
               pragma Loop_Invariant (Is_Acyclic (I, S.Nodes));
               pragma
                 Loop_Invariant
                   (Reachable_Set (I, S.Nodes)
                    <= Reachable_Set (S.Buckets (B), S.Nodes));
               pragma
                 Loop_Invariant
                   (LL_Sequence (I, S.Nodes)
                    <= LL_Sequence (S.Buckets (B), S.Nodes));

               --  E has not been found yet

               pragma
                 Loop_Invariant
                   (not Equivalent_Elements (S.Nodes (I).Element.V, E));
               pragma
                 Loop_Invariant
                   (for all K in
                      Interval'
                        (Last (LL_Sequence (I, S.Nodes)),
                         Last (LL_Sequence (S.Buckets (B), S.Nodes))) =>
                      not Equivalent_Elements
                            (S.Nodes
                               (Get (LL_Sequence (S.Buckets (B), S.Nodes), K))
                               .Element
                               .V,
                             E));

               pragma
                 Loop_Variant
                   (Decreases => Length (Reachable_Set (I, S.Nodes)));

               Lemma_Is_Acyclic_Def (I, S.Nodes);
               Lemma_Reachable_Def (I, S.Nodes);
               Lemma_LL_Sequence_Def (I, S.Nodes);

               P := I;
               I := S.Nodes (I).Next;
               if I = 0 then
                  pragma Assert (Pos = 0);
                  return;
               elsif Equivalent_Elements (S.Nodes (I).Element.V, E) then
                  pragma Assert (Pos = Last (LL_Sequence (I, S.Nodes)));

                  S.Nodes (P).Next := S.Nodes (I).Next;
                  S.Nodes (I).Has_Element := False;

                  --  I has been removed from S.Buckets (B)

                  begin
                     Lemma_Is_Acyclic_Def (I, Old_S.Nodes);
                     Lemma_Reachable_Def (I, Old_S.Nodes);
                     Lemma_LL_Sequence_Def (I, Old_S.Nodes);
                     Lemma_Is_Acyclic_Set
                       (S.Buckets (B),
                        P,
                        S.Nodes (I).Next,
                        Old_S.Nodes,
                        S.Nodes);
                     Lemma_Reachable_Set
                       (S.Buckets (B),
                        P,
                        S.Nodes (I).Next,
                        Old_S.Nodes,
                        S.Nodes);
                     Lemma_LL_Sequence_Set
                       (S.Buckets (B),
                        P,
                        S.Nodes (I).Next,
                        Old_S.Nodes,
                        S.Nodes);
                     pragma
                       Assert
                         (Range_Shifted
                            (LL_Sequence (S.Buckets (B), S.Nodes),
                             LL_Sequence (S.Buckets (B), Old_S.Nodes),
                             Pos,
                             Last (LL_Sequence (S.Buckets (B), S.Nodes)),
                             1));
                     pragma
                       Assert_And_Cut
                         (Is_Acyclic (S.Buckets (B), S.Nodes)
                          and
                            Reachable_Set (S.Buckets (B), S.Nodes)
                            = Remove
                                (Reachable_Set (S.Buckets (B), Old_S.Nodes), I)
                          and
                            Is_Remove
                              (LL_Sequence (S.Buckets (B), Old_S.Nodes),
                               Pos,
                               LL_Sequence (S.Buckets (B), S.Nodes)));
                  end;

                  exit;
               end if;
            end loop;
         end;
      end if;

      S.Length := S.Length - 1;
      Prove_Invariant (S, Old_S);
   end Delete_Key_No_Free;

   --------------------
   -- Delete_No_Free --
   --------------------

   procedure Delete_No_Free (S : in out Set; I : Positive_Count_Type) is
      B     : constant Hash_Type :=
        Find_Bucket (S.Nodes (I).Element.V, S.Modulus);
      Old_S : constant Set := S
      with Ghost;

      procedure Prove_Invariant (S, Old_S : Set)
      with
        Ghost,
        --  Reestablish the invariant
        Pre  =>
          LL_Correct (Old_S)
          and then LL_Complete (Old_S)
          and then LL_Has_Element (Old_S)
          and then Old_S.Capacity = S.Capacity
          and then Old_S.Modulus = S.Modulus
          and then S.Free = Old_S.Free
          and then I in 1 .. S.Capacity
          and then Old_S.Nodes (I).Element.V'Initialized
          and then B = Find_Bucket (Old_S.Nodes (I).Element.V, S.Modulus)
          and then
            (for all K in 1 .. S.Modulus =>
               (if K /= B then Old_S.Buckets (K) = S.Buckets (K)))
          and then Reachable (Old_S.Buckets (B), Old_S.Nodes, I)
          and then
            (for all I in 1 .. S.Capacity =>
               (if not Reachable (Old_S.Buckets (B), Old_S.Nodes, I)
                then Node_Preserved (S.Nodes (I), Old_S.Nodes (I))))
          and then
            (for all I of Reachable_Set (Old_S.Buckets (B), Old_S.Nodes) =>
               Node_Preserved
                 (S.Nodes (I),
                  (Old_S.Nodes (I)
                   with delta
                     Next        => S.Nodes (I).Next,
                     Has_Element => S.Nodes (I).Has_Element)))
          and then Is_Acyclic (S.Buckets (B), S.Nodes)
          and then
            Reachable_Set (S.Buckets (B), S.Nodes)
            = Remove (Reachable_Set (Old_S.Buckets (B), Old_S.Nodes), I)
          and then
            (for all I of Reachable_Set (S.Buckets (B), S.Nodes) =>
               S.Nodes (I).Has_Element)
          and then not S.Nodes (I).Has_Element
          and then
            Internal_Models.Find
              (LL_Sequence (Old_S.Buckets (B), Old_S.Nodes), I)
            > 0
          and then
            Is_Remove
              (LL_Sequence (Old_S.Buckets (B), Old_S.Nodes),
               Internal_Models.Find
                 (LL_Sequence (Old_S.Buckets (B), Old_S.Nodes), I),
               LL_Sequence (S.Buckets (B), S.Nodes)),
        Post =>
          LL_Correct (S)
          and then LL_Has_Element (S)
          and then not Is_Free (S.Free, S.Nodes, I)
          and then LL_Free (S) = LL_Free (Old_S)
          and then
            (for all K in 1 .. S.Modulus =>
               (if K /= B
                then
                  LL_Sequence (Old_S.Buckets (K), Old_S.Nodes)
                  = LL_Sequence (S.Buckets (K), S.Nodes)))
          and then
            (for all K in 1 .. S.Capacity =>
               (if K /= I
                then
                  Is_Free (S.Free, S.Nodes, K)
                  or else Is_Allocated (S.Buckets, S.Nodes, K)))
          and then
            Num_Allocated (S.Buckets, S.Nodes, S.Modulus)
            = Num_Allocated (Old_S.Buckets, Old_S.Nodes, S.Modulus) - 1
          and then LL_Model (S).Values <= LL_Model (Old_S).Values
          and then
            Keys_Included_Except
              (LL_Model (Old_S).Values, LL_Model (S).Values, I)
      is
      begin
         --  The free list is preserved

         if S.Free >= 0 then
            Lemma_Is_Acyclic_Preserved (S.Free, Old_S.Nodes, S.Nodes);
            Lemma_Reachable_Preserved (S.Free, Old_S.Nodes, S.Nodes);
            Lemma_LL_Sequence_Preserved (S.Free, Old_S.Nodes, S.Nodes);
         end if;

         --  Go through the bucket list to prove that other buckets are
         --  preserved.

         pragma
           Assert
             (for all K in 1 .. S.Modulus =>
                (if K /= B
                 then not Reachable (Old_S.Buckets (K), Old_S.Nodes, I)));

         for K in 1 .. S.Modulus loop
            if K /= B then
               Lemma_Is_Acyclic_Preserved
                 (S.Buckets (K), Old_S.Nodes, S.Nodes);
               Lemma_Reachable_Preserved (S.Buckets (K), Old_S.Nodes, S.Nodes);
               Lemma_LL_Sequence_Preserved
                 (S.Buckets (K), Old_S.Nodes, S.Nodes);
            else
               pragma
                 Assert
                   (By
                      (Num_Allocated (S.Buckets, S.Nodes, K)
                       = Num_Allocated (Old_S.Buckets, Old_S.Nodes, K) - 1,
                       Length (Reachable_Set (S.Buckets (B), S.Nodes))
                       = Length
                           (Reachable_Set (Old_S.Buckets (B), Old_S.Nodes))
                         - 1));
            end if;
            pragma
              Loop_Invariant
                (if K < B
                 then
                   Num_Allocated (S.Buckets, S.Nodes, K)
                   = Num_Allocated (Old_S.Buckets, Old_S.Nodes, K)
                 else
                   Num_Allocated (S.Buckets, S.Nodes, K)
                   = Num_Allocated (Old_S.Buckets, Old_S.Nodes, K) - 1);
            pragma
              Loop_Invariant
                (for all I in 1 .. K => Is_Acyclic (S.Buckets (I), S.Nodes));
            pragma
              Loop_Invariant
                (for all I in 1 .. K =>
                   (if I /= B
                    then
                      Reachable_Set (S.Buckets (I), S.Nodes)
                      = Reachable_Set (Old_S.Buckets (I), Old_S.Nodes)));
            pragma
              Loop_Invariant
                (for all I in 1 .. K =>
                   (if I /= B
                    then
                      LL_Sequence (Old_S.Buckets (I), Old_S.Nodes)
                      = LL_Sequence (S.Buckets (I), S.Nodes)));
            pragma
              Loop_Invariant
                (for all I in 1 .. K =>
                   (if I /= B
                    then
                      Length (Reachable_Set (S.Buckets (I), S.Nodes))
                      = Length
                          (Reachable_Set (Old_S.Buckets (I), Old_S.Nodes))));
         end loop;

         pragma
           Assert
             (for all K in 1 .. S.Capacity =>
                (if K /= I
                 then
                   Is_Allocated (S.Buckets, S.Nodes, K)
                   = Is_Allocated (Old_S.Buckets, Old_S.Nodes, K)));
         pragma Assert (LL_Correct (S));
         Lemma_Values_Preserved (Old_S, S, I);
         Lemma_Values_Buckets (S, B, I);
         Lemma_Values_Buckets (Old_S, B, I);
      end Prove_Invariant;

      procedure Prove_Length (S : Set)
      with
        Ghost,
        Pre  =>
          B in 1 .. S.Modulus and then LL_Correct (S) and then LL_Length (S),
        Post =>
          (if Internal_Models.Find (LL_Sequence (S.Buckets (B), S.Nodes), I)
             /= 0
           then S.Length > 0)
      is
      begin
         for K in B .. S.Modulus loop
            pragma
              Loop_Invariant
                (if Internal_Models.Find
                      (LL_Sequence (S.Buckets (B), S.Nodes), I)
                   /= 0
                 then Num_Allocated (S.Buckets, S.Nodes, K) > 0);
         end loop;
      end Prove_Length;

   begin

      --  Show that there is at least an allocated cell if I is allocated

      Prove_Length (S);

      if I = S.Buckets (B) then
         Lemma_Is_Acyclic_Def (I, S.Nodes);
         Lemma_Reachable_Def (I, S.Nodes);
         Lemma_LL_Sequence_Def (I, S.Nodes);

         S.Buckets (B) := S.Nodes (I).Next;
         S.Nodes (I).Has_Element := False;

         --  I has been removed from S.Buckets (B)

         Lemma_Is_Acyclic_Preserved (S.Buckets (B), Old_S.Nodes, S.Nodes);
         Lemma_Reachable_Preserved (S.Buckets (B), Old_S.Nodes, S.Nodes);
         Lemma_LL_Sequence_Preserved (S.Buckets (B), Old_S.Nodes, S.Nodes);
         pragma Assert (Is_Acyclic (S.Buckets (B), S.Nodes));
         pragma
           Assert
             (Reachable_Set (S.Buckets (B), S.Nodes)
              = Remove (Reachable_Set (Old_S.Buckets (B), Old_S.Nodes), I));
         pragma
           Assert
             (Is_Remove
                (LL_Sequence (Old_S.Buckets (B), Old_S.Nodes),
                 Internal_Models.Find
                   (LL_Sequence (Old_S.Buckets (B), Old_S.Nodes), I),
                 LL_Sequence (S.Buckets (B), S.Nodes)));
      else
         declare
            Capacity : constant Count_Type := S.Capacity;
            C        : Positive_Count_Type range 1 .. Capacity :=
              S.Buckets (B);
            N        : Positive_Count_Type range 1 .. Capacity;
         begin
            loop

               --  We are traversing the list rooted at S.Buckets (B) in
               --  S.Nodes.

               pragma Loop_Invariant (Is_Acyclic (C, S.Nodes));
               pragma
                 Loop_Invariant
                   (Reachable_Set (C, S.Nodes)
                    <= Reachable_Set (S.Buckets (B), S.Nodes));
               pragma
                 Loop_Invariant
                   (LL_Sequence (C, S.Nodes)
                    <= LL_Sequence (S.Buckets (B), S.Nodes));

               --  I has not been reached yet

               pragma Loop_Invariant (C /= I);
               pragma Loop_Invariant (Reachable (C, S.Nodes, I));
               pragma
                 Loop_Invariant
                   (for all K in
                      Interval'
                        (Last (LL_Sequence (C, S.Nodes)),
                         Last (LL_Sequence (S.Buckets (B), S.Nodes))) =>
                      Get (LL_Sequence (S.Buckets (B), S.Nodes), K) /= I);

               pragma
                 Loop_Variant
                   (Decreases => Length (Reachable_Set (C, S.Nodes)));

               Lemma_Is_Acyclic_Def (C, S.Nodes);
               Lemma_Reachable_Def (C, S.Nodes);
               Lemma_LL_Sequence_Def (C, S.Nodes);

               N := S.Nodes (C).Next;
               exit when N = I;
               C := N;
            end loop;
            pragma
              Assert
                (Last (LL_Sequence (N, S.Nodes))
                 = Internal_Models.Find
                     (LL_Sequence (Old_S.Buckets (B), Old_S.Nodes), I));
            Lemma_Is_Acyclic_Def (I, S.Nodes);
            Lemma_Reachable_Def (I, S.Nodes);
            Lemma_LL_Sequence_Def (I, S.Nodes);

            S.Nodes (C).Next := S.Nodes (I).Next;
            S.Nodes (I).Has_Element := False;

            --  I has been removed from S.Buckets (B)

            Lemma_Is_Acyclic_Set
              (S.Buckets (B), C, S.Nodes (I).Next, Old_S.Nodes, S.Nodes);
            Lemma_Reachable_Set
              (S.Buckets (B), C, S.Nodes (I).Next, Old_S.Nodes, S.Nodes);
            Lemma_LL_Sequence_Set
              (S.Buckets (B), C, S.Nodes (I).Next, Old_S.Nodes, S.Nodes);
            pragma Assert (Is_Acyclic (S.Buckets (B), S.Nodes));
            pragma
              Assert
                (Reachable_Set (S.Buckets (B), S.Nodes)
                 = Remove (Reachable_Set (S.Buckets (B), Old_S.Nodes), I));
            pragma
              Assert
                (Is_Remove
                   (LL_Sequence (Old_S.Buckets (B), Old_S.Nodes),
                    Internal_Models.Find
                      (LL_Sequence (Old_S.Buckets (B), Old_S.Nodes), I),
                    LL_Sequence (S.Buckets (B), S.Nodes)));

         end;
      end if;

      S.Length := S.Length - 1;
      Prove_Invariant (S, Old_S);
   end Delete_No_Free;

   -------------
   -- Element --
   -------------

   function Element (S : Set; I : Positive_Count_Type) return Element_Type is
   begin
      return S.Nodes (I).Element.V;
   end Element;

   ---------------
   -- Empty_Set --
   ---------------

   function Empty_Set (Capacity : Count_Type) return Set is
      Modulus : constant Positive_Hash_Type := Default_Modulus (Capacity);
      V       : Relaxed_Element;
   begin
      return
         S : Set :=
           (Capacity => Capacity,
            Modulus  => Modulus,
            Nodes    => (1 .. Capacity => (V, 0, False)),
            Buckets  => (1 .. Modulus => 0),
            Free     => -1,
            Length   => 0)
      do
         for B in 1 .. Modulus loop
            pragma Loop_Invariant (Num_Allocated (S.Buckets, S.Nodes, B) = 0);
         end loop;
      end return;
   end Empty_Set;

   ----------
   -- Find --
   ----------

   function Find (S : Set; E : Element_Type) return Count_Type is
      B        : constant Hash_Type := Find_Bucket (E, S.Modulus);
      Capacity : constant Count_Type := S.Capacity;
      C        : Count_Type range 0 .. Capacity := S.Buckets (B);

      procedure Prove_Length (S : Set)
      with
        Ghost,
        Pre  =>
          B in 1 .. S.Modulus and then LL_Correct (S) and then LL_Length (S),
        Post =>
          (if Internal_Models.Find
                (LL_Sequence (S.Buckets (B), S.Nodes), LL_Model (S).Values, E)
             /= 0
           then S.Length > 0)
      is
      begin
         for K in B .. S.Modulus loop
            pragma
              Loop_Invariant
                (if Internal_Models.Find
                      (LL_Sequence (S.Buckets (B), S.Nodes),
                       LL_Model (S).Values,
                       E)
                   /= 0
                 then Num_Allocated (S.Buckets, S.Nodes, K) > 0);
         end loop;
      end Prove_Length;

   begin
      if S.Length = 0 then
         Prove_Length (S);
         return 0;
      end if;

      while C /= 0 loop
         pragma Loop_Invariant (Is_Acyclic (C, S.Nodes));
         pragma
           Loop_Invariant
             (LL_Sequence (C, S.Nodes)
              <= LL_Sequence (S.Buckets (B), S.Nodes));
         pragma
           Loop_Invariant
             (for all K in
                Interval'
                  (Last (LL_Sequence (C, S.Nodes)) + 1,
                   Last (LL_Sequence (S.Buckets (B), S.Nodes))) =>
                not Equivalent_Elements
                      (S.Nodes (Get (LL_Sequence (S.Buckets (B), S.Nodes), K))
                         .Element
                         .V,
                       E));
         pragma
           Loop_Variant (Decreases => Length (Reachable_Set (C, S.Nodes)));

         if Equivalent_Elements (S.Nodes (C).Element.V, E) then
            return C;
         end if;
         Lemma_Is_Acyclic_Def (C, S.Nodes);
         Lemma_Reachable_Def (C, S.Nodes);
         Lemma_LL_Sequence_Def (C, S.Nodes);
         C := S.Nodes (C).Next;
      end loop;
      return 0;
   end Find;

   -----------
   -- First --
   -----------

   function First (S : Set) return Count_Type is
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
                Length (LL_Sequence (S.Buckets (K), S.Nodes)) = 0);
         pragma Loop_Invariant (Num_Allocated (S.Buckets, S.Nodes, B) = 0);
      end loop;

      raise Program_Error;
   end First;

   -----------------
   -- Has_Element --
   -----------------

   function Has_Element (S : Set; I : Positive_Count_Type) return Boolean is
      M : constant Set_LL_Model := LL_Model (S)
      with Ghost;
   begin
      pragma
        Assert
          (if I <= S.Capacity and then Is_Allocated (S.Buckets, S.Nodes, I)
           then
             Find
               (S.Nodes,
                S.Buckets (Find_Bucket (Get (M.Values, I), S.Modulus)),
                I)
             > 0);
      return I <= S.Capacity and then S.Nodes (I).Has_Element;
   end Has_Element;

   --------------------
   -- Insrt_Internal --
   --------------------

   procedure Insert_Internal
     (S : in out Set; I : Positive_Count_Type; E : Element_Type)
   is
      B           : constant Hash_Type := Find_Bucket (E, S.Modulus);
      Old_S       : constant Set := S
      with Ghost;
      Old_Nodes   : constant Nodes_Type := S.Nodes
      with Ghost;
      Old_Buckets : constant Buckets_Type := S.Buckets
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

         Lemma_Is_Acyclic_Def (S.Buckets (B), S.Nodes);
         Lemma_Is_Acyclic_Preserved (Old_Bucket, Old_Nodes, S.Nodes);
         Lemma_Reachable_Def (S.Buckets (B), S.Nodes);
         Lemma_Reachable_Preserved (Old_Bucket, Old_Nodes, S.Nodes);
         Lemma_LL_Sequence_Def (S.Buckets (B), S.Nodes);
         Lemma_LL_Sequence_Preserved (Old_Bucket, Old_Nodes, S.Nodes);
         pragma
           Assert
             (Reachable_Set (S.Buckets (B), S.Nodes)
              = Add (Reachable_Set (Old_Bucket, Old_Nodes), I));
         pragma
           Assert
             (Is_Add
                (LL_Sequence (Old_Bucket, Old_Nodes),
                 I,
                 LL_Sequence (S.Buckets (B), S.Nodes)));

         --  The free list is preserved

         if S.Free >= 0 then
            Lemma_Is_Acyclic_Preserved (S.Free, Old_Nodes, S.Nodes);
            Lemma_Reachable_Preserved (S.Free, Old_Nodes, S.Nodes);
            Lemma_LL_Sequence_Preserved (S.Free, Old_Nodes, S.Nodes);
            pragma
              Assert
                (for all I of Reachable_Set (S.Free, S.Nodes) =>
                   not Reachable (S.Buckets (B), S.Nodes, I));
         else
            pragma
              Assert
                (if S.Free < 0
                 then
                   (for all I in -S.Free .. S.Capacity =>
                      not Reachable (S.Buckets (B), S.Nodes, I)));
         end if;

         --  Go through the bucket list to prove that other buckets are
         --  preserved.

         for K in 1 .. S.Modulus loop
            if B /= K then
               Lemma_Is_Acyclic_Preserved (S.Buckets (K), Old_Nodes, S.Nodes);
               Lemma_Reachable_Preserved (S.Buckets (K), Old_Nodes, S.Nodes);
               Lemma_LL_Sequence_Preserved (S.Buckets (K), Old_Nodes, S.Nodes);
            end if;
            pragma
              Loop_Invariant
                (if K < B
                 then
                   Num_Allocated (S.Buckets, S.Nodes, K)
                   = Num_Allocated (Old_Buckets, Old_Nodes, K)
                 else
                   Num_Allocated (S.Buckets, S.Nodes, K)
                   = Num_Allocated (Old_Buckets, Old_Nodes, K) + 1);
            pragma
              Loop_Invariant
                (for all I in 1 .. K => Is_Acyclic (S.Buckets (I), S.Nodes));
            pragma
              Loop_Invariant
                (for all I in 1 .. K =>
                   (if I /= B
                    then
                      Reachable_Set (S.Buckets (I), S.Nodes)
                      = Reachable_Set (Old_Buckets (I), Old_Nodes)));
            pragma
              Loop_Invariant
                (for all I in 1 .. K =>
                   (if I /= B
                    then
                      LL_Sequence (Old_Buckets (I), Old_Nodes)
                      = LL_Sequence (S.Buckets (I), S.Nodes)));
            pragma
              Loop_Invariant
                (for all I in 1 .. K =>
                   (if I /= B
                    then
                      Length (Reachable_Set (S.Buckets (I), S.Nodes))
                      = Length (Reachable_Set (Old_Buckets (I), Old_Nodes))));
         end loop;

         pragma
           Assert
             (for all K in 1 .. S.Capacity =>
                (if K /= I
                 then
                   Is_Allocated (S.Buckets, S.Nodes, K)
                   = Is_Allocated (Old_Buckets, Old_Nodes, K)));
         pragma Assert (LL_Correct (S));
         Lemma_Values_Preserved (Old_S, S, I);
         pragma Assert (Get (Values_From_Nodes (S), I) = E);
      end Prove_Invariant;

   begin
      S.Nodes (I) := ((V => E), S.Buckets (B), True);
      S.Buckets (B) := I;
      S.Length := S.Length + 1;

      Prove_Invariant;
   end Insert_Internal;

   --------------
   -- Is_Empty --
   --------------

   function Is_Empty (S : Set) return Boolean is
      M : constant Set_LL_Model := LL_Model (S)
      with Ghost;

      procedure Prove_Post with Ghost is
      begin
         for K in 1 .. S.Modulus loop
            pragma
              Loop_Invariant
                (if Default_Init (S)
                 then Num_Allocated (S.Buckets, S.Nodes, K) = 0);
            pragma
              Loop_Invariant
                (Num_Allocated (M.Buckets, K)
                 = Num_Allocated (S.Buckets, S.Nodes, K));
         end loop;
      end Prove_Post;

   begin
      Prove_Post;
      return S.Length = 0;
   end Is_Empty;

   ------------
   -- Length --
   ------------

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
                 = Num_Allocated (S.Buckets, S.Nodes, B));
         end loop;
      end Prove_Post;
   begin
      Prove_Post;
      return S.Length;
   end Length;

   ----------
   -- Next --
   ----------

   function Next (S : Set; I : Positive_Count_Type) return Count_Type is
      B : constant Hash_Type := Find_Bucket (S.Nodes (I).Element.V, S.Modulus)
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
            pragma Loop_Invariant (Is_Acyclic (C, S.Nodes));
            pragma
              Loop_Invariant
                (LL_Sequence (C, S.Nodes)
                 <= LL_Sequence (S.Buckets (B), S.Nodes));
            pragma
              Loop_Invariant
                (for all K in
                   Interval'
                     (Last (LL_Sequence (C, S.Nodes)) + 1,
                      Last (LL_Sequence (S.Buckets (B), S.Nodes))) =>
                   Get (LL_Sequence (S.Buckets (B), S.Nodes), K) /= I);
            pragma
              Loop_Variant (Decreases => Length (LL_Sequence (C, S.Nodes)));
            Lemma_Is_Acyclic_Def (C, S.Nodes);
            Lemma_LL_Sequence_Def (C, S.Nodes);
            exit when C = I;
            C := S.Nodes (C).Next;
         end loop;
         if S.Nodes (I).Next /= 0 then
            Lemma_LL_Sequence_Def (S.Nodes (I).Next, S.Nodes);
         end if;
      end Unfold_LL_Sequence;

      B_N : Hash_Type range 1 .. S.Modulus;
   begin
      Unfold_LL_Sequence;

      if S.Nodes (I).Next /= 0 then
         pragma
           Assert (Internal_Models.Find (LL_Model (S).Buckets (B), I) > 1);
         return S.Nodes (I).Next;
      end if;

      B_N := Find_Bucket (S.Nodes (I).Element.V, S.Modulus);

      while B_N < S.Modulus loop
         pragma Loop_Variant (Increases => B_N);
         pragma Loop_Invariant (B_N >= B);
         pragma
           Loop_Invariant
             (for all K in B + 1 .. B_N =>
                Length (LL_Sequence (S.Buckets (K), S.Nodes)) = 0);
         B_N := B_N + 1;
         if S.Buckets (B_N) /= 0 then
            pragma Assert (Length (LL_Model (S).Buckets (B_N)) > 0);
            return S.Buckets (B_N);
         end if;
      end loop;
      return 0;
   end Next;

   -------------
   -- Replace --
   -------------

   procedure Replace
     (S : in out Set; I : Positive_Count_Type; E : Element_Type) is
   begin
      Lemma_Equivalent_Elements_Find_Bucket
        (S.Nodes (I).Element.V, E, S.Modulus);
      Replace_Internal (S, I, E);
   end Replace;

   ---------------------
   -- Replace_Element --
   ---------------------

   procedure Replace_Element
     (S : in out Set; I : Positive_Count_Type; E : Element_Type)
   is
      Old_S : constant Set := S
      with Ghost;

   begin
      Lemma_Equivalent_Elements_Find_Bucket
        (S.Nodes (I).Element.V, E, S.Modulus);

      if Find_Bucket (S.Nodes (I).Element.V, S.Modulus)
        = Find_Bucket (E, S.Modulus)
      then
         Replace_Internal (S, I, E);
         return;
      end if;

      declare
         Capacity : constant Count_Type := S.Capacity;
         C        : Count_Type range 0 .. Capacity :=
           S.Buckets (Find_Bucket (E, S.Modulus));
      begin
         while C /= 0 loop
            pragma Loop_Invariant (Is_Acyclic (C, S.Nodes));
            pragma
              Loop_Invariant
                (LL_Sequence (C, S.Nodes)
                 <= LL_Sequence
                      (S.Buckets (Find_Bucket (E, S.Modulus)), S.Nodes));
            pragma
              Loop_Variant (Decreases => Length (LL_Sequence (C, S.Nodes)));
            if Equivalent_Elements (S.Nodes (C).Element.V, E) then
               raise Program_Error with "attempt to replace existing element";
            end if;
            Lemma_Is_Acyclic_Def (C, S.Nodes);
            Lemma_LL_Sequence_Def (C, S.Nodes);
            C := S.Nodes (C).Next;
         end loop;
      end;

      Delete_No_Free (S, I);
      Insert_Internal (S, I, E);
   end Replace_Element;

   ----------------------
   -- Replace_Internal --
   ----------------------

   procedure Replace_Internal
     (S : in out Set; I : Positive_Count_Type; E : Element_Type)
   is
      Old_S : Set := S
      with Ghost;

      procedure Prove_Invariant (S, Old_S : Set)
        --  Prove the invariant when an element is replaced by an equivalent one
      with
        Ghost,
        Pre  =>
          LL_Invariant (Old_S)
          and then Old_S.Capacity = S.Capacity
          and then Old_S.Modulus = S.Modulus
          and then I in 1 .. S.Capacity
          and then S.Length = Old_S.Length
          and then S.Free = Old_S.Free
          and then S.Buckets = Old_S.Buckets
          and then
            Reachable (S.Buckets (Find_Bucket (E, S.Modulus)), Old_S.Nodes, I)
          and then
            (for all J in 1 .. S.Capacity =>
               (if I /= J then Node_Preserved (Old_S.Nodes (J), S.Nodes (J))))
          and then
            Node_Preserved
              ((Old_S.Nodes (I) with delta Element => (V => E)), S.Nodes (I)),
        Post =>
          LL_Invariant (S)
          and then Same_Keys (LL_Model (Old_S).Values, LL_Model (S).Values)
          and then
            Elements_Equal_Except
              (LL_Model (Old_S).Values, LL_Model (S).Values, I)
          and then Get (LL_Model (S).Values, I) = E
          and then LL_Model (S).Buckets = LL_Model (Old_S).Buckets
      is
      begin
         --  The free list is preserved

         if S.Free >= 0 then
            Lemma_Is_Acyclic_Preserved (S.Free, Old_S.Nodes, S.Nodes);
            Lemma_Reachable_Preserved (S.Free, Old_S.Nodes, S.Nodes);
            Lemma_LL_Sequence_Preserved (S.Free, Old_S.Nodes, S.Nodes);
            pragma
              Assert
                (Reachable_Set (S.Free, Old_S.Nodes)
                 = Reachable_Set (S.Free, Old_S.Nodes));
         end if;

         --  Go through the bucket list to prove that buckets are preserved

         for K in 1 .. S.Modulus loop
            Lemma_Is_Acyclic_Preserved (S.Buckets (K), Old_S.Nodes, S.Nodes);
            Lemma_Reachable_Preserved (S.Buckets (K), Old_S.Nodes, S.Nodes);
            Lemma_LL_Sequence_Preserved (S.Buckets (K), Old_S.Nodes, S.Nodes);
            pragma
              Loop_Invariant
                (Num_Allocated (S.Buckets, S.Nodes, K)
                 = Num_Allocated (Old_S.Buckets, Old_S.Nodes, K));
            pragma
              Loop_Invariant
                (for all I in 1 .. K => Is_Acyclic (S.Buckets (I), S.Nodes));
            pragma
              Loop_Invariant
                (for all I in 1 .. K =>
                   Reachable_Set (S.Buckets (I), S.Nodes)
                   = Reachable_Set (Old_S.Buckets (I), Old_S.Nodes));
            pragma
              Loop_Invariant
                (for all I in 1 .. K =>
                   LL_Sequence (Old_S.Buckets (I), Old_S.Nodes)
                   = LL_Sequence (S.Buckets (I), S.Nodes));
            pragma
              Loop_Invariant
                (for all I in 1 .. K =>
                   Length (Reachable_Set (S.Buckets (I), S.Nodes))
                   = Length (Reachable_Set (S.Buckets (I), Old_S.Nodes)));
         end loop;

         pragma Assert (LL_Correct (S));
         Lemma_Values_Preserved (Old_S, S, I);
         Lemma_Values_Buckets (S, Find_Bucket (E, S.Modulus), I);
         Lemma_Values_Buckets (Old_S, Find_Bucket (E, S.Modulus), I);
      end Prove_Invariant;
   begin
      S.Nodes (I).Element := (V => E);
      Prove_Invariant (S, Old_S);
   end Replace_Internal;

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

end Data_Structure.Basic_Operations;
