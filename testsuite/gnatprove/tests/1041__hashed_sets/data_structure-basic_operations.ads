with SPARK.Big_Integers;             use SPARK.Big_Integers;
with SPARK.Big_Intervals;            use SPARK.Big_Intervals;
with SPARK.Containers.Functional.Maps;
with SPARK.Containers.Functional.Sets;
with SPARK.Containers.Functional.Infinite_Sequences;
with Data_Structure.Internal_Models; use Data_Structure.Internal_Models;

private package Data_Structure.Basic_Operations
  with SPARK_Mode, Always_Terminates
is

   package Basic_Model
     with Ghost
   is

      --  Invariant: The buckets and free lists are well formed and they do not
      --  overlap.

      function LL_Correct (S : Set) return Boolean;

      use Memory_Index_Sequences;
      use Index_To_Value_Maps;

      --  Low level model of a set:
      --    * An association from memory indexes to values,
      --    * A sequence of memory indexes per bucket

      type Mem_Seq_Array is array (Hash_Type range 1 .. <>) of Sequence;

      type Set_LL_Model
        (Capacity : Count_Type;
         Modulus  : Positive_Hash_Type)
      is record
         Values  : Values_Type;
         Buckets : Mem_Seq_Array (1 .. Modulus);
      end record
      with
        Predicate =>
          (for all B in 1 .. Modulus =>
             (for all I of Buckets (B) => I in 1 .. Capacity));

      --  Extracts the abstract low-level model (values map and per-bucket
      --  sequences) from a set.
      function LL_Model (S : Set) return Set_LL_Model
      with
        Pre  => LL_Correct (S),
        Post =>
          LL_Model'Result.Capacity = S.Capacity
          and then LL_Model'Result.Modulus = S.Modulus
          and then
            (for all B in 1 .. S.Modulus =>
               (for all I of LL_Model'Result.Buckets (B) =>
                  Has_Key (LL_Model'Result.Values, I)));

      function Num_Allocated
        (Buckets : Mem_Seq_Array; B : Hash_Type) return Big_Natural
      is (Length (Buckets (B))
          + (if B = 1 then 0 else Num_Allocated (Buckets, B - 1)))
      with Pre => B in Buckets'Range, Subprogram_Variant => (Decreases => B);

      function Num_Allocated (Buckets : Mem_Seq_Array) return Big_Natural
      is (Num_Allocated (Buckets, Buckets'Last))
      with Pre => Buckets'Length > 0;

      --  Invariant on the low level model
      function LL_Invariant (S : Set) return Boolean
      with Post => (if LL_Invariant'Result then LL_Correct (S));

      --  Proves each bucket's sequence has no duplicate indexes, and every
      --  node is in the correct bucket.
      procedure Lemma_LL_No_Duplicated_Indexes (S : Set)
      with
        Pre  => LL_Correct (S),
        Post =>
          (for all B in 1 .. S.Modulus =>
             No_Duplicated_Indexes (LL_Model (S).Buckets (B)))
          and then
            (for all B in 1 .. S.Modulus =>
               (for all I of LL_Model (S).Buckets (B) =>
                  Find_Bucket (Get (LL_Model (S).Values, I), S.Modulus) = B));

      --  Returns the index of the first non-empty bucket at or after B
      function First_Non_Empty_Bucket
        (Buckets : Mem_Seq_Array; B : Positive_Hash_Type)
         return Positive_Hash_Type
      with
        Pre  =>
          B in Buckets'Range
          and then
            (for some B2 in B .. Buckets'Last => Length (Buckets (B2)) /= 0),
        Post =>
          First_Non_Empty_Bucket'Result in B .. Buckets'Last
          and then Length (Buckets (First_Non_Empty_Bucket'Result)) /= 0
          and then
            (for all B2 in B .. First_Non_Empty_Bucket'Result - 1 =>
               Length (Buckets (B2)) = 0);

      --  Proves the low-level invariant holds on a default-initialized set
      procedure Prove_Invariant_On_Default (S : Set)
      with
        Ghost,
        Post =>
          (if Default_Init (S)
           then
             LL_Invariant (S)
             and then Num_Allocated (LL_Model (S).Buckets) = 0);
   end Basic_Model;

   use Basic_Model;
   use Memory_Index_Sequences;
   use Index_To_Value_Maps;

   pragma Unevaluated_Use_Of_Old (Allow);

   --  Number of elements currently in the set
   function Length (S : Set) return Count_Type
   with
     Pre  => LL_Invariant (S),
     Post =>
       To_Big (Length'Result) = Num_Allocated (LL_Model (S).Buckets)
       and then Length'Result <= S.Capacity;

   --  Whether the set contains no elements
   function Is_Empty (S : Set) return Boolean
   with
     Pre  => LL_Invariant (S),
     Post =>
       Is_Empty'Result = (Num_Allocated (LL_Model (S).Buckets) = 0)
       and (if Default_Init (S) then Is_Empty'Result);

   --  Creates an empty set with the given Capacity
   function Empty_Set (Capacity : Count_Type) return Set
   with
     Post =>
       LL_Invariant (Empty_Set'Result)
       and then Length (Empty_Set'Result) = 0
       and then Empty_Set'Result.Capacity = Capacity;

   --  Whether index I refers to an allocated element in the set
   function Has_Element (S : Set; I : Positive_Count_Type) return Boolean
   with
     Pre  => LL_Invariant (S),
     Post =>
       (if Has_Element'Result
        then
          I <= S.Capacity
          and then Has_Key (LL_Model (S).Values, I)
          and then
            Internal_Models.Find
              (LL_Model (S).Buckets
                 (Find_Bucket (Get (LL_Model (S).Values, I), S.Modulus)),
               I)
            > 0
        else
          I > S.Capacity
          or else
            (for all B in 1 .. S.Modulus =>
               Internal_Models.Find (LL_Model (S).Buckets (B), I) = 0));

   --  Returns the element stored at index I
   function Element (S : Set; I : Positive_Count_Type) return Element_Type
   with
     Pre      => LL_Invariant (S) and then Has_Element (S, I),
     Post     => Element'Result = Get (LL_Model (S).Values, I),
     Annotate => (GNATprove, Inline_For_Proof);

   --  Returns the index of the element equivalent to E, or 0 if not present
   function Find (S : Set; E : Element_Type) return Count_Type
   with
     Pre  => LL_Invariant (S),
     Post =>
       Find'Result
       = (declare
            I : constant Big_Natural :=
              Find
                (LL_Model (S).Buckets (Find_Bucket (E, S.Modulus)),
                 LL_Model (S).Values,
                 E);
          begin
            (if I = 0
             then 0
             else Get (LL_Model (S).Buckets (Find_Bucket (E, S.Modulus)), I)));

   --  Whether an element equivalent to E is in the set
   function Contains (S : Set; E : Element_Type) return Boolean
   with
     Pre  => LL_Invariant (S),
     Post =>
       Contains'Result
       = (Find
            (LL_Model (S).Buckets (Find_Bucket (E, S.Modulus)),
             LL_Model (S).Values,
             E)
          /= 0);

   --  Returns the first element index in iteration order, or 0 if empty
   function First (S : Set) return Count_Type
   with
     Pre  => LL_Invariant (S),
     Post =>
       (if Length (S) = 0
        then First'Result = 0
        else
          First'Result in 1 .. S.Capacity
          and then Has_Key (LL_Model (S).Values, First'Result)
          and then
            (declare
               B : constant Hash_Type :=
                 First_Non_Empty_Bucket (LL_Model (S).Buckets, 1);
             begin
               First'Result
               = Get
                   (LL_Model (S).Buckets (B),
                    Last (LL_Model (S).Buckets (B)))));

   --  Returns the element index following I in iteration order, or 0 if I is
   --  last.
   function Next (S : Set; I : Positive_Count_Type) return Count_Type
   with
     Pre  => LL_Invariant (S) and then Has_Element (S, I),
     Post =>
       (declare
          B : constant Hash_Type :=
            Find_Bucket (Get (LL_Model (S).Values, I), S.Modulus);
        begin
          (if Internal_Models.Find (LL_Model (S).Buckets (B), I) > 1
           then
             Next'Result
             = Get
                 (LL_Model (S).Buckets (B),
                  Internal_Models.Find (LL_Model (S).Buckets (B), I) - 1)
           elsif B = S.Modulus
             or else
               (for all K in B + 1 .. S.Modulus =>
                  Length (LL_Model (S).Buckets (K)) = 0)
           then Next'Result = 0
           else
             Next'Result <= S.Capacity
             and then
               (declare
                  B_N : constant Hash_Type :=
                    First_Non_Empty_Bucket (LL_Model (S).Buckets, B + 1);
                begin
                  Next'Result
                  = Get
                      (LL_Model (S).Buckets (B_N),
                       Last (LL_Model (S).Buckets (B_N))))));

   --  Inserts E if not already present; returns its index I and whether it
   --  was inserted.
   procedure Conditional_Insert
     (S        : in out Set;
      E        : Element_Type;
      I        : out Count_Type;
      Inserted : out Boolean)
   with
     Pre  =>
       LL_Invariant (S)
       and then (Length (S) < S.Capacity or else Contains (S, E)),
     Post =>
       LL_Invariant (S)
       and then Inserted = not Contains (S, E)'Old
       and then I > 0
       and then I <= S.Capacity
       and then
         (if not Inserted
          then
            Internal_Models.Find
              (LL_Model (S).Buckets (Find_Bucket (E, S.Modulus)), I)
            /= 0
            and then Equivalent_Elements (Get (LL_Model (S).Values, I), E)
            and then LL_Model (S) = LL_Model (S)'Old
          else
            Length (S) = Length (S)'Old + 1
            and then
              Is_Add
                (LL_Model (S)'Old.Buckets (Find_Bucket (E, S.Modulus)),
                 I,
                 LL_Model (S).Buckets (Find_Bucket (E, S.Modulus)))
            and then
              (for all K in 1 .. S.Modulus =>
                 (if K /= Find_Bucket (E, S.Modulus)
                  then
                    LL_Model (S).Buckets (K) = LL_Model (S).Buckets'Old (K)))
            and then LL_Model (S).Values'Old <= LL_Model (S).Values
            and then
              Keys_Included_Except
                (LL_Model (S).Values, LL_Model (S).Values'Old, I)
            and then Get (LL_Model (S).Values, I) = E);

   --  Replaces the element at I with E, which must be equivalent to the
   --  current element.
   procedure Replace
     (S : in out Set; I : Positive_Count_Type; E : Element_Type)
   with
     Pre  =>
       LL_Invariant (S)
       and then Has_Element (S, I)
       and then Equivalent_Elements (Get (LL_Model (S).Values, I), E),
     Post =>
       LL_Invariant (S)
       and then Get (LL_Model (S).Values, I) = E
       and then LL_Model (S).Buckets = LL_Model (S).Buckets'Old
       and then Same_Keys (LL_Model (S).Values'Old, LL_Model (S).Values)
       and then
         Elements_Equal_Except
           (LL_Model (S).Values'Old, LL_Model (S).Values, I);

   --  Removes the element at index I from the set
   procedure Delete (S : in out Set; I : Positive_Count_Type)
   with
     Pre  => LL_Invariant (S) and then Has_Element (S, I),
     Post =>
       LL_Invariant (S)
       and then Length (S) = Length (S)'Old - 1
       and then
         (declare
            B : constant Positive_Hash_Type :=
              Find_Bucket (Get (LL_Model (S).Values, I), S.Modulus)'Old;
          begin
            Is_Remove
              (LL_Model (S)'Old.Buckets (B),
               Internal_Models.Find (LL_Model (S)'Old.Buckets (B), I),
               LL_Model (S).Buckets (B))
            and then
              (for all K in 1 .. S.Modulus =>
                 (if B /= K
                  then
                    LL_Model (S).Buckets (K) = LL_Model (S).Buckets'Old (K))))
       and then LL_Model (S).Values <= LL_Model (S).Values'Old
       and then
         Keys_Included_Except
           (LL_Model (S).Values'Old, LL_Model (S).Values, I);

   --  Removes the element equivalent to E, if present
   procedure Delete_Key (S : in out Set; E : Element_Type)
   with
     Pre  => LL_Invariant (S),
     Post =>
       LL_Invariant (S)
       and then
         (declare
            B : constant Positive_Hash_Type := Find_Bucket (E, S.Modulus);
            P : constant Big_Natural :=
              Find (LL_Model (S)'Old.Buckets (B), LL_Model (S)'Old.Values, E);
            I : constant Count_Type :=
              (if P = 0 then 0 else Get (LL_Model (S)'Old.Buckets (B), P));
          begin
            (if P = 0
             then LL_Model (S) = LL_Model (S)'Old
             else
               Is_Remove
                 (LL_Model (S)'Old.Buckets (B), P, LL_Model (S).Buckets (B))
               and then Length (S) = Length (S)'Old - 1
               and then
                 (for all K in 1 .. S.Modulus =>
                    (if B /= K
                     then
                       LL_Model (S).Buckets (K)
                       = LL_Model (S).Buckets'Old (K)))
               and then LL_Model (S).Values <= LL_Model (S).Values'Old
               and then
                 Keys_Included_Except
                   (LL_Model (S).Values'Old, LL_Model (S).Values, I)));

   --  Replaces the element at I with E, moving the node to a different
   --  bucket if needed.
   procedure Replace_Element
     (S : in out Set; I : Positive_Count_Type; E : Element_Type)
   with
     Pre  =>
       LL_Invariant (S)
       and then Has_Element (S, I)
       and then
         (Equivalent_Elements (Get (LL_Model (S).Values, I), E)
          or else not Contains (S, E)),
     Post =>
       LL_Invariant (S)
       and then Same_Keys (LL_Model (S).Values'Old, LL_Model (S).Values)
       and then
         Elements_Equal_Except
           (LL_Model (S).Values'Old, LL_Model (S).Values, I)
       and then Get (LL_Model (S).Values, I) = E
       and then
         (declare
            B_Old : constant Positive_Hash_Type :=
              Find_Bucket (Get (LL_Model (S).Values, I), S.Modulus)'Old;
            B_New : constant Positive_Hash_Type := Find_Bucket (E, S.Modulus);
          begin
            (if B_Old = B_New
             then LL_Model (S).Buckets = LL_Model (S).Buckets'Old
             else
               Is_Remove
                 (LL_Model (S)'Old.Buckets (B_Old),
                  Internal_Models.Find (LL_Model (S)'Old.Buckets (B_Old), I),
                  LL_Model (S).Buckets (B_Old))
               and then
                 Is_Add
                   (LL_Model (S)'Old.Buckets (B_New),
                    I,
                    LL_Model (S).Buckets (B_New))
               and then
                 (for all K in 1 .. S.Modulus =>
                    (if B_New /= K and then B_Old /= K
                     then
                       LL_Model (S).Buckets (K)
                       = LL_Model (S).Buckets'Old (K)))));

end Data_Structure.Basic_Operations;
