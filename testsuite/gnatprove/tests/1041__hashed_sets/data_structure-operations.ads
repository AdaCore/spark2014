with SPARK.Big_Integers;              use SPARK.Big_Integers;
with SPARK.Big_Intervals;             use SPARK.Big_Intervals;
with Data_Structure.Internal_Models;  use Data_Structure.Internal_Models;
with Data_Structure.Basic_Operations; use Data_Structure.Basic_Operations;

private package Data_Structure.Operations
  with SPARK_Mode, Always_Terminates
is
   package Advanced_Model
     with Ghost
   is
      use Basic_Model;

      use Memory_Index_Sequences;
      use Index_To_Value_Maps;

      --  High level model of a set:
      --    * An association from memory indexes to values,
      --    * A sequence of allocated memory indexes in the iteration order

      type Set_HL_Model is record
         Values            : Values_Type;
         Allocated_Indexes : Sequence;
      end record;

      --  Extracts the high-level model (values map and allocated-index
      --  sequence) from a set.
      function HL_Model (S : Set) return Set_HL_Model
      with
        Pre  => Basic_Model.LL_Invariant (S),
        Post =>
          (for all I of HL_Model'Result.Allocated_Indexes =>
             Has_Key (HL_Model'Result.Values, I));

      --  High level invariant, there are no duplicated element in the set

      function No_Duplicated_Elements
        (B : Sequence; Values : Values_Type) return Boolean
      is (for all P1 in Interval'(1, Last (B)) =>
            (for all P2 in Interval'(1, Last (B)) =>
               (if P1 /= P2
                then
                  not Equivalent_Elements
                        (Get (Values, Get (B, P1)),
                         Get (Values, Get (B, P2))))))
      with Pre => (for all I of B => Has_Key (Values, I));

      function HL_No_Duplicated_Elements (S : Set) return Boolean
      is (No_Duplicated_Elements
            (HL_Model (S).Allocated_Indexes, HL_Model (S).Values))
      with Pre => LL_Invariant (S);

      function HL_Invariant (S : Set) return Boolean
      is (LL_Invariant (S) and then HL_No_Duplicated_Elements (S));

      --  Proves the allocated-index sequence of a set has no duplicate indexes
      procedure Lemma_HL_No_Duplicated_Indexes (S : Set)
      with
        Pre  => LL_Invariant (S),
        Post => No_Duplicated_Indexes (HL_Model (S).Allocated_Indexes);

      --  Proves the high-level invariant holds on a default-initialized set
      procedure Prove_Invariant_On_Default (S : Set)
      with Ghost, Post => (if Default_Init (S) then HL_Invariant (S));

   end Advanced_Model;

   use Advanced_Model;
   use Memory_Index_Sequences;
   use Index_To_Value_Maps;

   pragma Unevaluated_Use_Of_Old (Allow);

   --  Creates an empty set with the given Capacity
   function Empty_Set (Capacity : Count_Type) return Set
   with
     Post =>
       HL_Invariant (Empty_Set'Result)
       and then Last (HL_Model (Empty_Set'Result).Allocated_Indexes) = 0
       and then Empty_Set'Result.Capacity = Capacity;

   --  Whether I is the index of an allocated element in the set
   function Has_Element (S : Set; I : Positive_Count_Type) return Boolean
   with
     Pre  => HL_Invariant (S),
     Post =>
       Has_Element'Result
       = (Internal_Models.Find (HL_Model (S).Allocated_Indexes, I) /= 0);

   --  Returns the index of the element equivalent to E, or 0 if not present
   function Find (S : Set; E : Element_Type) return Count_Type
   with
     Pre  => HL_Invariant (S),
     Post =>
       Find'Result
       = (declare
            I : constant Big_Natural :=
              Internal_Models.Find
                (HL_Model (S).Allocated_Indexes, HL_Model (S).Values, E);
          begin
            (if I = 0 then 0 else Get (HL_Model (S).Allocated_Indexes, I)));

   --  Whether an element equivalent to E is in the set
   function Contains (S : Set; E : Element_Type) return Boolean
   with
     Pre  => HL_Invariant (S),
     Post =>
       Contains'Result
       = (Internal_Models.Find
            (HL_Model (S).Allocated_Indexes, HL_Model (S).Values, E)
          /= 0);

   --  Returns the first element index in iteration order, or 0 if empty
   function First (S : Set) return Count_Type
   with
     Pre  => HL_Invariant (S),
     Post =>
       (if Length (HL_Model (S).Allocated_Indexes) = 0
        then First'Result = 0
        else
          First'Result > 0
          and then First'Result = Get (HL_Model (S).Allocated_Indexes, 1));

   --  Returns the element index following I in iteration order, or 0 if I is
   --  last.
   function Next (S : Set; I : Positive_Count_Type) return Count_Type
   with
     Pre  => HL_Invariant (S) and then Has_Element (S, I),
     Post =>
       (declare
          P : constant Big_Positive :=
            Internal_Models.Find (HL_Model (S).Allocated_Indexes, I);
        begin
          (if P = Last (HL_Model (S).Allocated_Indexes)
           then Next'Result = 0
           else Next'Result = Get (HL_Model (S).Allocated_Indexes, P + 1)));

   --  Returns the element stored at index I
   function Element (S : Set; I : Positive_Count_Type) return Element_Type
   with
     Pre      => HL_Invariant (S) and then Has_Element (S, I),
     Post     => Element'Result = Get (HL_Model (S).Values, I),
     Annotate => (GNATprove, Inline_For_Proof);

   --  Number of elements in the set
   function Length (S : Set) return Count_Type
   with
     Pre  => HL_Invariant (S),
     Post =>
       To_Big (Length'Result) = Length (HL_Model (S).Allocated_Indexes)
       and then Length'Result <= S.Capacity;

   --  Whether the set contains no elements
   function Is_Empty (S : Set) return Boolean
   with
     Pre  => HL_Invariant (S),
     Post =>
       Is_Empty'Result = (Length (HL_Model (S).Allocated_Indexes) = 0)
       and (if Default_Init (S) then Is_Empty'Result);

   --  Inserts E if not already present; returns its index I and whether it
   --  was inserted.
   procedure Conditional_Insert
     (S        : in out Set;
      E        : Element_Type;
      I        : out Positive_Count_Type;
      Inserted : out Boolean)
   with
     Pre  =>
       HL_Invariant (S)
       and then (Length (S) < S.Capacity or else Contains (S, E)),
     Post =>
       HL_Invariant (S)
       and then Inserted = not Contains (S, E)'Old
       and then Has_Element (S, I)
       and then
         (if Inserted
          then
            (declare
               P : constant Big_Positive :=
                 Internal_Models.Find (HL_Model (S).Allocated_Indexes, I);
             begin
               Is_Add
                 (HL_Model (S).Allocated_Indexes'Old,
                  P,
                  I,
                  HL_Model (S).Allocated_Indexes)
               and then HL_Model (S).Values'Old <= HL_Model (S).Values
               and then Has_Key (HL_Model (S).Values, I)
               and then Get (HL_Model (S).Values, I) = E)
          else
            Equivalent_Elements (Get (HL_Model (S).Values, I), E)
            and then HL_Model (S) = HL_Model (S)'Old);

   --  Removes the element at index I
   procedure Delete (S : in out Set; I : Positive_Count_Type)
   with
     Pre  => HL_Invariant (S) and then Has_Element (S, I),
     Post =>
       HL_Invariant (S)
       and then not Has_Element (S, I)
       and then
         (declare
            P : constant Big_Positive :=
              Internal_Models.Find (HL_Model (S).Allocated_Indexes'Old, I);
          begin
            Is_Remove
              (HL_Model (S).Allocated_Indexes'Old,
               P,
               HL_Model (S).Allocated_Indexes)
            and then HL_Model (S).Values <= HL_Model (S).Values'Old);

   --  Removes the element equivalent to E, if present
   procedure Delete_Key (S : in out Set; E : Element_Type)
   with
     Pre  => HL_Invariant (S),
     Post =>
       HL_Invariant (S)
       and then not Contains (S, E)
       and then
         (if not Contains (S, E)'Old
          then HL_Model (S) = HL_Model (S)'Old
          else
            (declare
               P : constant Big_Positive :=
                 Find
                   (HL_Model (S).Allocated_Indexes'Old,
                    HL_Model (S).Values'Old,
                    E);
             begin
               Is_Remove
                 (HL_Model (S).Allocated_Indexes'Old,
                  P,
                  HL_Model (S).Allocated_Indexes)
               and then HL_Model (S).Values <= HL_Model (S).Values'Old));

   --  Replaces the element at I with E, moving the node to a different bucket if needed
   procedure Replace_Element
     (S : in out Set; I : Positive_Count_Type; E : Element_Type)
   with
     Pre  =>
       HL_Invariant (S)
       and then Has_Element (S, I)
       and then
         (Equivalent_Elements (Get (HL_Model (S).Values, I), E)
          or else not Contains (S, E)),
     Post =>
       HL_Invariant (S)
       and then
         Elements_Equal_Except
           (HL_Model (S).Values, HL_Model (S).Values'Old, I)
       and then Has_Key (HL_Model (S).Values, I)
       and then Get (HL_Model (S).Values, I) = E
       and then
         Length (HL_Model (S).Allocated_Indexes)
         = Length (HL_Model (S).Allocated_Indexes)'Old
       and then
         (if Internal_Models.Find (HL_Model (S).Allocated_Indexes'Old, I)
            /= Internal_Models.Find (HL_Model (S).Allocated_Indexes, I)
          then
            Is_Move
              (HL_Model (S).Allocated_Indexes'Old,
               Internal_Models.Find (HL_Model (S).Allocated_Indexes'Old, I),
               Internal_Models.Find (HL_Model (S).Allocated_Indexes, I),
               HL_Model (S).Allocated_Indexes)
          else
            HL_Model (S).Allocated_Indexes'Old
            = HL_Model (S).Allocated_Indexes);

   --  Replaces the element at I with an equivalent value E (same bucket)
   procedure Replace
     (S : in out Set; I : Positive_Count_Type; E : Element_Type)
   with
     Pre  =>
       HL_Invariant (S)
       and then Has_Element (S, I)
       and then Equivalent_Elements (Get (HL_Model (S).Values, I), E),
     Post =>
       HL_Invariant (S)
       and then
         Elements_Equal_Except
           (HL_Model (S).Values, HL_Model (S).Values'Old, I)
       and then Has_Key (HL_Model (S).Values, I)
       and then Get (HL_Model (S).Values, I) = E
       and then
         Length (HL_Model (S).Allocated_Indexes)
         = Length (HL_Model (S).Allocated_Indexes)'Old
       and then
         HL_Model (S).Allocated_Indexes'Old = HL_Model (S).Allocated_Indexes;
end Data_Structure.Operations;
