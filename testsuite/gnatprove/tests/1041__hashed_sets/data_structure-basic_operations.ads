pragma Extensions_Allowed (On);

with SPARK.Big_Integers;     use SPARK.Big_Integers;
with SPARK.Big_Intervals;    use SPARK.Big_Intervals;
with SPARK.Containers.Functional.Maps;
with SPARK.Containers.Functional.Sets;
with SPARK.Containers.Functional.Infinite_Sequences;

package Data_Structure.Basic_Operations with
   SPARK_Mode,
   Always_Terminates
is

   package Basic_Model with Ghost is
      package Memory_Index_To_Big is new Signed_Conversions (Count_Type);
      function To_Big (X : Count_Type) return Big_Integer renames
        Memory_Index_To_Big.To_Big_Integer;

      --  Invariant: The buckets and free lists are well formed and they do not overlap

      function LL_Correct (S : Set) return Boolean;

      --  Lower level model of a set

      package Memory_Index_Sequences is new SPARK.Containers.Functional.Infinite_Sequences
        (Positive_Count_Type);
      use Memory_Index_Sequences;

      function Is_Add (S1 : Sequence; I : Positive_Count_Type; S2 : Sequence) return Boolean is
        (Length (S2) - 1 = Length (S1) and then Get (S2, Last (S2)) = I and then S1 <= S2);

      function Is_Remove (S1 : Sequence; P : Big_Positive; S2 : Sequence) return Boolean is
        (Length (S2) = Length (S1) - 1 and then P <= Last (S1)
         and then Range_Equal (S1, S2, 1, P - 1)
         and then Range_Shifted (S2, S1, P, Last (S2), 1));

      package Index_To_Value_Maps is new SPARK.Containers.Functional.Maps
        (Positive_Count_Type, Element_Type);
      use Index_To_Value_Maps;

      type Mem_Seq_Array is array (Hash_Type range 1 .. <>) of Sequence;
      subtype Values_Type is Index_To_Value_Maps.Map;

      --  Low level model of a set:
      --    * An association from memory indexes to values,
      --    * A sequence of memory indexes per bucket

      type Set_LL_Model (Capacity : Count_Type; Modulus : Positive_Hash_Type) is record
         Values  : Values_Type;
         Buckets : Mem_Seq_Array (1 .. Modulus);
      end record with
        Predicate =>
          (for all B in 1 .. Modulus =>
             (for all I of Buckets (B) => I in 1 .. Capacity));

      function "=" (S1, S2 : Set_LL_Model) return Boolean is
        (S1.Values = S2.Values and then S1.Buckets = S2.Buckets);

      function Find (S : Sequence; I : Positive_Count_Type) return Big_Natural with
        Post => Find'Result <= Last (S)
        and then (if Find'Result > 0 then Get (S, Find'Result) = I)
        and then (for all K in Interval'(Find'Result + 1, Last (S)) => Get (S, K) /= I);

      function Find (S : Sequence; V : Values_Type; E : Element_Type) return Big_Natural with
        Pre  => (for all I of S => Has_Key (V, I)),
        Post => Find'Result <= Last (S)
        and then (if Find'Result > 0 then Equivalent_Elements (Get (V, Get (S, Find'Result)), E))
        and then (for all K in Interval'(Find'Result + 1, Last (S)) => not Equivalent_Elements (Get (V, Get (S, K)), E));

      function LL_Model (S : Set) return Set_LL_Model with
        Pre => LL_Correct (S),
        Post => LL_Model'Result.Capacity = S.Capacity
        and then LL_Model'Result.Modulus = S.Modulus
        and then
          (for all B in 1 .. S.Modulus =>
             (for all I of LL_Model'Result.Buckets (B) => Has_Key (LL_Model'Result.Values, I)));

      function Num_Allocated (Buckets : Mem_Seq_Array; B : Hash_Type) return Big_Natural is
        (Length (Buckets (B))
         + (if B = 1 then 0 else Num_Allocated (Buckets, B - 1)))
      with Pre => B in Buckets'Range,
        Subprogram_Variant => (Decreases => B);

      function Num_Allocated (Buckets : Mem_Seq_Array) return Big_Natural is
        (Num_Allocated (Buckets, Buckets'Last))
      with Pre => Buckets'Length > 0;

      function No_Duplicated_Indexes (B : Sequence) return Boolean is
        (for all P1 in Interval'(2, Last (B)) =>
           (for all P2 in Interval'(1, P1 - 1) => Get (B, P2) /= Get (B, P1)));

      --  Invariant on the low level model
      function LL_Invariant (S : Set) return Boolean with
        Post => (if LL_Invariant'Result then LL_Correct (S));

      procedure Lemma_LL_No_Duplicated_Indexes (S : Set) with
        Pre  => LL_Correct (S),
        Post => (for all B in 1 .. S.Modulus =>
                   No_Duplicated_Indexes (LL_Model (S).Buckets (B)));

      function First_Non_Empty_Bucket (Buckets : Mem_Seq_Array; B : Positive_Hash_Type) return Positive_Hash_Type with
        Pre  => B in Buckets'Range
        and then (for some B2 in B .. Buckets'Last => Length (Buckets (B2)) /= 0),
        Post => First_Non_Empty_Bucket'Result in B .. Buckets'Last
           and then Length (Buckets (First_Non_Empty_Bucket'Result)) /= 0
           and then (for all B2 in B .. First_Non_Empty_Bucket'Result - 1 =>
                       Length (Buckets (B2)) = 0);
   end Basic_Model;

   use Basic_Model;
   use Basic_Model.Memory_Index_Sequences;
   use Basic_Model.Index_To_Value_Maps;

   pragma Unevaluated_Use_Of_Old (Allow);

   function Length (S : Set) return Count_Type with
     Pre  => LL_Invariant (S);

   function Empty_Set (Capacity : Count_Type) return Set with
     Post => LL_Invariant (Empty_Set'Result)
     and then Length (Empty_Set'Result) = 0;

   function Has_Element (S : Set; I : Positive_Count_Type) return Boolean with
     Pre  => LL_Invariant (S),
     Post =>
       (if Has_Element'Result
        then I <= S.Capacity
        and then Has_Key (LL_Model (S).Values, I)
        and then Basic_Model.Find (LL_Model (S).Buckets (Find_Bucket (Get (LL_Model (S).Values, I), S.Modulus)), I) > 0
        else I > S.Capacity
        or else (for all B in 1 .. S.Modulus => Basic_Model.Find (LL_Model (S).Buckets (B), I) = 0));

   function Contains (S : Set; E : Element_Type) return Boolean with
     Pre  => LL_Invariant (S),
     Post => Contains'Result =
       (Find (LL_Model (S).Buckets (Find_Bucket (E, S.Modulus)), LL_Model (S).Values, E) /= 0);

   function First (S : Set) return Count_Type with
     Pre  => LL_Invariant (S),
     Post =>
       (if Length (S) = 0 then First'Result = 0
        else First'Result in 1 .. S.Capacity
        and then Has_Key (LL_Model (S).Values, First'Result)
        and then
          (declare
              B : constant Hash_Type := First_Non_Empty_Bucket (LL_Model (S).Buckets, 1);
           begin
             First'Result = Get (LL_Model (S).Buckets (B), Last (LL_Model (S).Buckets (B)))));

   function Next (S : Set; I : Positive_Count_Type) return Count_Type with
     Pre  => LL_Invariant (S)
     and then Has_Element (S, I),
     Post =>
       (declare
          B : constant Hash_Type := Find_Bucket (Get (LL_Model (S).Values, I), S.Modulus);
        begin
          (if Basic_Model.Find (LL_Model (S).Buckets (B), I) > 1
           then Next'Result = Get (LL_Model (S).Buckets (B), Basic_Model.Find (LL_Model (S).Buckets (B), I) - 1)
           elsif B = S.Modulus
             or else (for all K in B + 1 .. S.Modulus => Length (LL_Model (S).Buckets (K)) = 0)
           then Next'Result = 0
           else
             Next'Result <= S.Capacity
             and then
               (declare
                  B_N : constant Hash_Type := First_Non_Empty_Bucket (LL_Model (S).Buckets, B + 1);
                begin
                  Next'Result = Get (LL_Model (S).Buckets (B_N), Last (LL_Model (S).Buckets (B_N))))));

   procedure Conditional_Insert (S : in out Set; E : Element_Type; I : out Count_Type; Inserted : out Boolean) with
     Pre  => LL_Invariant (S)
     and then S.Length < S.Capacity,
     Post => LL_Invariant (S)
     and then Inserted = not Contains (S, E)'Old and then I > 0
     and then I <= S.Capacity
     and then
       (if not Inserted
        then Basic_Model.Find (LL_Model (S).Buckets (Find_Bucket (E, S.Modulus)), I) /= 0
        and then Equivalent_Elements (Get (LL_Model (S).Values, I), E)
        and then LL_Model (S) = LL_Model (S)'Old
        else Length (S) = Length (S)'Old + 1
        and then Is_Add (LL_Model (S)'Old.Buckets (Find_Bucket (E, S.Modulus)), I, LL_Model (S).Buckets (Find_Bucket (E, S.Modulus)))
        and then
          (for all K in 1 .. S.Modulus =>
             (if K /= Find_Bucket (E, S.Modulus) then LL_Model (S).Buckets (K) = LL_Model (S).Buckets'Old (K)))
        and then LL_Model (S).Values'Old <= LL_Model (S).Values
        and then Keys_Included_Except (LL_Model (S).Values, LL_Model (S).Values'Old, I)
        and then Get (LL_Model (S).Values, I) = E);

   procedure Delete (S : in out Set; I : Positive_Count_Type) with
     Pre  => LL_Invariant (S)
       and then Has_Element (S, I),
     Post => LL_Invariant (S)
     and then Length (S) = Length (S)'Old - 1
     and then
       (declare
          B : constant Positive_Hash_Type := Find_Bucket (Get (LL_Model (S).Values, I), S.Modulus)'Old;
        begin
          Is_Remove (LL_Model (S)'Old.Buckets (B),
                     Basic_Model.Find (LL_Model (S)'Old.Buckets (B), I),
                     LL_Model (S).Buckets (B))
          and then
           (for all K in 1 .. S.Modulus =>
              (if B /= K
               then LL_Model (S).Buckets (K) = LL_Model (S).Buckets'Old (K))))
      and then LL_Model (S).Values <= LL_Model (S).Values'Old
      and then Keys_Included_Except (LL_Model (S).Values'Old, LL_Model (S).Values, I);

   procedure Delete_Key (S : in out Set; E : Element_Type) with
     Pre  => LL_Invariant (S),
     Post => LL_Invariant (S)
     and then
         (declare
            B : constant Positive_Hash_Type := Find_Bucket (E, S.Modulus);
            P : constant Big_Natural := Find (LL_Model (S)'Old.Buckets (B), LL_Model (S)'Old.Values, E);
            I : constant Count_Type :=
              (if P = 0 then 0 else Get (LL_Model (S)'Old.Buckets (B), P));
          begin
            (if P = 0
             then LL_Model (S) = LL_Model (S)'Old
             else Is_Remove (LL_Model (S)'Old.Buckets (B), P, LL_Model (S).Buckets (B))
               and then Length (S) = Length (S)'Old - 1
               and then
                 (for all K in 1 .. S.Modulus =>
                    (if B /= K then LL_Model (S).Buckets (K) = LL_Model (S).Buckets'Old (K)))
               and then LL_Model (S).Values <= LL_Model (S).Values'Old
               and then Keys_Included_Except (LL_Model (S).Values'Old, LL_Model (S).Values, I)));

   procedure Replace_Element (S : in out Set; I : Positive_Count_Type; E : Element_Type) with
     Pre  => LL_Invariant (S)
       and then Has_Element (S, I)
       and then (Equivalent_Elements (Get (LL_Model (S).Values, I), E) or else not Contains (S, E)),
     Post => LL_Invariant (S)
     and then Same_Keys (LL_Model (S).Values'Old, LL_Model (S).Values)
     and then Elements_Equal_Except (LL_Model (S).Values'Old, LL_Model (S).Values, I)
     and then Get (LL_Model (S).Values, I) = E
     and then
       (declare
          B_Old : constant Positive_Hash_Type := Find_Bucket (S.Memory (I).Value.V, S.Modulus)'Old;
          B_New : constant Positive_Hash_Type := Find_Bucket (E, S.Modulus);
        begin
          (if B_Old = B_New
           then LL_Model (S).Buckets = LL_Model (S).Buckets'Old
           else Is_Remove (LL_Model (S)'Old.Buckets (B_Old),
                           Basic_Model.Find (LL_Model (S)'Old.Buckets (B_Old), I),
                           LL_Model (S).Buckets (B_Old))
           and then Is_Add (LL_Model (S)'Old.Buckets (B_New), I, LL_Model (S).Buckets (B_New))
           and then
             (for all K in 1 .. S.Modulus =>
                (if B_New /= K and then B_Old /= K
                 then LL_Model (S).Buckets (K) = LL_Model (S).Buckets'Old (K)))));

end Data_Structure.Basic_Operations;
