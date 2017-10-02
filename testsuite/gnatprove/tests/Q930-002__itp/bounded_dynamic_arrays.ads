generic
   type Component is private;
   type List_Index is range <> with Predicate => 1 in List_Index;
   type List is array (List_Index range <>) of Component;
   Default_Value : Component;
   with function "=" (Left, Right : List) return Boolean is <>;
package Bounded_Dynamic_Arrays is
   pragma Pure;

--     pragma Compile_Time_Error (1 not in List_Index, "List_Index must include the value 1");
--     --  We are using a 1-based array representation

   Null_List : constant List (List_Index'First .. List_Index'First - 1) := (others => Default_Value);

   Maximum_Length : constant List_Index := List_Index'Last;
   --  The physical maximum for the upper bound of the wrapped List array
   --  values.  Defined for readability in predicates.

   subtype Natural_Index is List_Index'Base range 0 .. Maximum_Length;

   subtype Index is List_Index range 1 .. Maximum_Length;

   type Sequence (Capacity : Natural_Index) is private;
   --  A wrapper for List array values in which Capacity represents the
   --  physical upper bound. Capacity is, therefore, the maximum number
   --  of Component values possibly contained by the given Sequence instance.

   function Null_Sequence return Sequence with
     Post => Null_Sequence'Result.Capacity = 0 and
             Length (Null_Sequence'Result) = 0 and
             Value (Null_Sequence'Result) = Null_List;

   function Instance (Capacity : Natural_Index; Content : List) return Sequence with
     Pre  => Content'Length <= Capacity,
     Post => Instance'Result.Capacity = Capacity and
             Length (Instance'Result) = Content'Length and
             Value (Instance'Result) = Content;

   function Instance (Capacity : Natural_Index; C : Component) return Sequence with
     Pre  => Capacity >= 1,
     Post => Length (Instance'Result) = 1 and
             Value (Instance'Result) (1) = C and
             Instance'Result.Capacity = Capacity;

   function Instance (Content : List) return Sequence with
     Pre  => Content'Length <= Maximum_Length,
     Post => Length (Instance'Result) = Content'Length and
             Value (Instance'Result) = Content and
             Instance'Result.Capacity = Content'Length;

   function Value (This : Sequence) return List with
     Post => Value'Result'Length = Length (This) and
             Value'Result'First = 1 and
             Value'Result'Last = Length (This) and
             (Length (This) > 0) = not Empty (This),
     Inline;
   --  Returns the content of this sequence. The value returned is the
   --  "logical" value in that only that slice which is currently assigned
   --  is returned, as opposed to the entire physical representation.

   function Value (This : Sequence; Location : Index) return Component with
     Pre => Location <= Length (This),
     Inline;

   function Empty (This : Sequence) return Boolean with
     Post=> Empty'Result = (Length (This) = 0),
     Inline;

   procedure Clear (This : out Sequence) with
     Post => Length (This) = 0 and Empty (This),
     Inline;
   --  Sets the given sequence to contain nothing.

   function "=" (Left, Right : Sequence) return Boolean with
     Inline;
   --  Returns whether the (logical) values of the two sequences are identical.

   function Length (This : Sequence) return Natural_Index with
     Inline;
   --  Returns the logical length of This, i.e., the length of the slice of
   --  This that is currently assigned a value.

   function "&" (Left : Sequence; Right : Sequence) return Sequence with
     Pre  => Length (Left) + Length (Right) <= Maximum_Length,
     Post => Value ("&"'Result) = Value (Left) & Value (Right) and
             Length ("&"'Result) = Length (Left) + Length (Right) and
             "&"'Result.Capacity = Length (Left) + Length (Right);

   function "&" (Left : Sequence; Right : List) return Sequence with
     Pre  => Length (Left) + Right'Length <= Maximum_Length,
     Post => Value ("&"'Result) = Value (Left) & Right and
             Length ("&"'Result) = Length (Left) + Right'Length and
             "&"'Result.Capacity = Length (Left) + Right'Length;

   function "&" (Left : List; Right : Sequence) return Sequence with
     Pre  => Left'Length + Length (Right) <= Maximum_Length,
     Post => Value ("&"'Result) = Left & Value (Right) and
             Length ("&"'Result) = Left'Length + Length (Right) and
             "&"'Result.Capacity = Left'Length + Length (Right);

   function "&" (Left : Sequence; Right : Component) return Sequence with
     Pre  => Length (Left) + 1 <= Maximum_Length,
     Post => Value ("&"'Result) = Value (Left) & Right and
             Length ("&"'Result) = Length (Left) + 1 and
             "&"'Result.Capacity = Length (Left) + 1;

   function "&" (Left : Component; Right : Sequence) return Sequence with
     Pre  => 1 + Length (Right) <= Maximum_Length,
     Post => Value ("&"'Result) = Left & Value (Right) and
             Length ("&"'Result) = 1 + Length (Right) and
             "&"'Result.Capacity = 1 + Length (Right);

   procedure Copy (Source : Sequence; To : in out Sequence) with
     Pre  => To.Capacity >= Length (Source),
     Post => Value (To) = Value (Source) and
             Length (To) = Length (Source) and
             To = Source;
   --  Copies the logical value of Source, the RHS, to the LHS sequence To. The
   --  prior value of To is lost.

   procedure Copy (Source : List; To : in out Sequence) with
     Pre  => To.Capacity >= Source'Length,
     Post => Value (To) = Source and
             Length (To) = Source'Length;
   --  Copies the value of the array Source, the RHS, to the LHS sequence To.
   --  The prior value of To is lost.

   procedure Copy (Source : Component; To : in out Sequence) with
     Pre  => To.Capacity > 0,
     Post => Value (To) (1) = Source and
             Length (To) = 1;
   --  Copies the value of the individual array component Source, the RHS, to
   --  the LHS sequence To. The prior value of To is lost.

   procedure Append (Tail : Sequence; To : in out Sequence) with
     Pre  => Length (Tail) + Length (To) in 1 .. To.Capacity,
     Post => Value (To) = Value (To'Old) & Value (Tail) and
             Length (To) = Length (To'Old) + Length (Tail);

   procedure Append (Tail : List; To : in out Sequence) with
     Pre  => Tail'Length + Length (To) in 1 .. To.Capacity,
     Post => Value (To) = Value (To'Old) & Tail and
             Length (To) = Length (To'Old) + Tail'Length;

   procedure Append (Tail : Component; To : in out Sequence) with
     Pre  => 1 + Length (To) <= To.Capacity,
     Post => Value (To) = Value (To'Old) & Tail and
             Length (To) = Length (To'Old) + 1;

   procedure Ammend (This : in out Sequence; By : Sequence; Start : Index) with
     Pre  => Start + Length (By) - 1 in 1 .. This.Capacity,
     Post => Value (This) (Start .. Start + Length (By) - 1) = Value (By) and
             (if Start + Length (By) - 1 > Length (This'Old)
                then Length (This) = Start + Length (By) - 1
                else Length (This) = Length (This'Old));
   --  Overwrites the content of This, beginning at array index Start, with the
   --  logical value of the Sequence argument By

   procedure Ammend (This : in out Sequence; By : List; Start : Index) with
     Pre  => Start + By'Length - 1 in 1 .. This.Capacity,
     Post => Value (This) (Start .. Start + By'Length - 1) = By and
             (if Start + By'Length - 1 > Length (This'Old)
                then Length (This) = Start + By'Length - 1
                else Length (This) = Length (This'Old));
   --  Overwrites the content of This, beginning at array index Start, with the
   --  value of List argument By

   procedure Ammend (This : in out Sequence; By : Component; Start : Index) with
     Pre  => Start <= Length (This),
     Post => Value (This) (Start) = By and
             Length (This) = Length (This)'Old;
   --  Overwrites the content of This, at array index Start, with the value of
   --  the single Component argument By

   function Location (Fragment : Sequence; Within : Sequence) return Natural_Index;
   --  TODO: add postcondition
   --  Returns the starting index of the logical value of the sequence Fragment
   --  in the sequence Within, if any. Returns 0 when the fragment is not
   --  found.
   --  NB: The implementation is not the best algorithm...

   function Location (Fragment : List; Within : Sequence) return Natural_Index with
     Post => Location'Result in 0 .. Within.Capacity and
             (if not Contains (Within, Fragment) then
                Location'Result = 0
              else
                Location'Result > 0);
             --  (Location'Result > 0) = Contains (Within, Fragment);
   --  Returns the starting index of the value of the array Fragment in the
   --  sequence Within, if any. Returns 0 when the fragment is not found.
   --  NB: The implementation is a simple linear search...

   function Location (Fragment : Component; Within : Sequence) return Natural_Index with
     Post => Location'Result in 0 .. Within.Capacity and
             (Location'Result > 0) = Contains (Within, Fragment);
   --  Returns the index of the value of the component Fragment within the
   --  sequence Within, if any. Returns 0 when the fragment is not found.

   function Contains (Within : Sequence; Fragment : Component) return Boolean with
     Ghost;

   function Contains (Within : Sequence; Fragment : List) return Boolean with
     Ghost;
   --  When Fragment'Length = 0, ie for a null array, we return 0. Likewise,
   --  when Fragment'Length is longer than the content of Within, we return 0.
   --  Both the above inputs are allowed and normal.

private

   type Sequence (Capacity : Natural_Index) is record
      Current_Length : Natural_Index := 0;
      Content        : List (1 .. Capacity) := (others => Default_Value);
   end record
     with Predicate => Current_Length in 0 .. Capacity;

   ------------
   -- Length --
   ------------

   function Length (This : Sequence) return Natural_Index is
     (This.Current_Length);

   -----------
   -- Value --
   -----------

   function Value (This : Sequence) return List is
     (This.Content (1 .. This.Current_Length));

   -----------
   -- Value --
   -----------

   function Value (This : Sequence; Location : Index) return Component is
     (This.Content (Location));

   -----------
   -- Empty --
   -----------

   function Empty (This : Sequence) return Boolean is
     (This.Current_Length = 0);

   ---------
   -- "=" --
   ---------

   function "=" (Left, Right : Sequence) return Boolean is
     (Value (Left) = Value (Right));

   --------------
   -- Contains --
   --------------

   function Contains (Within : Sequence; Fragment : Component) return Boolean is
     (for some K in 1 .. Length (Within) =>
        Within.Content (K) = Fragment);

   --------------
   -- Contains --
   --------------

   function Contains (Within : Sequence; Fragment : List) return Boolean is
     (Fragment'Length in 1 .. Within.Current_Length
      --  ie, Fragment'Length > 0 but is not too long
      and then
      (for some K in 1 .. (Within.Current_Length - Fragment'Length + 1) =>
           Within.Content (K .. (K + Fragment'Length - 1)) = Fragment));

end Bounded_Dynamic_Arrays;
