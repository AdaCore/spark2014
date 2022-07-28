package Q with SPARK_Mode is
   subtype Contained_Element is Character;  -- temp generic actual param for now
   subtype Formal_Integer is Integer;       -- temp generic actual param for now

   type Set is private with
     Default_Initial_Condition => Empty (Set),
     Iterable => (First       => First_Iter_Index,
                  Next        => Next_Iter_Index,
                  Has_Element => Iter_Has_Element,
                  Element     => Iter_Element);

   pragma Unevaluated_Use_Of_Old (Allow);

   function Empty (This : Set) return Boolean;

   function Null_Set return Set;

   subtype Cursor is Formal_Integer;

   function As_Cursor (E : Contained_Element) return Cursor is
     (Contained_Element'Pos (E));

   function Valid_Contained_Element (C : Cursor) return Boolean is
     (C >= Contained_Element'Pos (Contained_Element'First) and then
      C <= Contained_Element'Pos (Contained_Element'Last));
   --  Returns whether C is in Contained_Element'Range

   Sentinel : constant Cursor := As_Cursor (Contained_Element'Last) + 1;
   --  The cursor signaling iteration is complete.
   pragma Assert (not Valid_Contained_Element (Sentinel));

   First_Cursor : constant Cursor := As_Cursor (Contained_Element'First);
   --  a convenience constant

   function Is_Next_Cursor (This : Set; Result, Start : Cursor) return Boolean with
     Pre => Start = Sentinel or else Valid_Contained_Element (Start);

   function First_Iter_Index (This : Set) return Cursor with
     Post => First_Iter_Index'Result = Sentinel or else
             Is_Next_Cursor (This, First_Iter_Index'Result, Start => First_Cursor);
   --  Returns the first cursor for which This (C) is True, or the Sentinel
   --  value indicating iteration completion.

   function Next_Iter_Index (This : Set; Position : Cursor) return Cursor with
     Pre  => Position < Cursor'Last and then
             Valid_Contained_Element (Position),
     Post => Next_Iter_Index'Result = Sentinel or else
             Is_Next_Cursor (This, Next_Iter_Index'Result, Start => Position + 1);
   --  Returns the next cursor for which This (C) is True, starting after
   --  Position, or returns the Sentinel value indicating iteration completion.

   function Iter_Has_Element (Unused : Set;  Position : Cursor) return Boolean;
   --  Logically, returns whether Unused (Position) is True. However,
   --  First_Iter_Index and Next_Iter_Index only return cursor values for those
   --  components that are True, or the Sentinel value indicating the end of
   --  the iteration. Therefore all this function need to do is check for the
   --  Sentinel.

   function Iter_Element (Unused : Set; Position : Cursor) return Contained_Element with
     Pre => Valid_Contained_Element (Position);
   --  Logically, Unused (Position) is true, so this function returns the
   --  Contained_Element value corresponding to Position (because iteration
   --  over Set objects provides Contained_Element values).

private

   type Set is array (Contained_Element) of Boolean with Default_Component_Value => False;

   function Empty (This : Set) return Boolean is
     (This = Null_Set);

   function Null_Set return Set is
     (others => False);

   function As_Contained_Element (N : Cursor) return Contained_Element is
     (Contained_Element'Val (Cursor'Pos (N)))
   with Pre => Valid_Contained_Element (N);

   function Is_Next_Cursor (This : Set; Result, Start : Cursor) return Boolean is
     (Valid_Contained_Element (Result)     and then
      This (As_Contained_Element (Result)) and then
      --  there were no true components before Result, beginning at Start
      (if Result > Start then
         (for all K in Start .. Result - 1 => not This (As_Contained_Element (K)))));

   function None_True (This : Set; From : Cursor) return Boolean is
     (for all K in As_Contained_Element (From) .. Contained_Element'Last => not This (K))
   with Pre => Valid_Contained_Element (From);

   function Next_True (This : Set; Start : Cursor) return Cursor with
     Pre  => Valid_Contained_Element (Start) or else Start = Sentinel,
     Post => (if Start = Sentinel or else None_True (This, From => Start)
              then Next_True'Result = Sentinel
              else Is_Next_Cursor (This, Next_True'Result, Start));

end Q;
