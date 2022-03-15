package body Sequences with SPARK_Mode is
   function Length (Container : List) return Big_Natural
   with Subprogram_Variant => (Structural => Container);

   function Length (Container : List) return Big_Natural is
     (if Container = null then 0 else 1 + Length (Container.Next));

   function Length (Container : Sequence) return Big_Natural is
     (Length (List (Container)));

   function Get
     (Container : List;
      Position  : Big_Positive) return Element_Type is
     (if Position = 1 then Container.Value.all
      else Get (Container.Next, Position - 1))
   with Pre => Position <= Length (Container),
       Subprogram_Variant => (Decreases => Position);

   function Get
     (Container : Sequence;
      Position  : Big_Positive) return Element_Type
   is (Get (List (Container), Position));

   function Last (Container : Sequence) return Big_Natural is
     (Length (Container));

   ------------------------
   -- Property Functions --
   ------------------------

   function "=" (Left : Sequence; Right : Sequence) return Boolean is
     (Length (Left) = Length (Right)
      and then (for all N in Left => Get (Left, N) = Get (Right, N)));

   function "<" (Left : Sequence; Right : Sequence) return Boolean  is
     (Length (Left) < Length (Right)
      and then (for all N in Left =>
                     Get (Left, N) = Get (Right, N)));

   function "<=" (Left : Sequence; Right : Sequence) return Boolean  is
     (Length (Left) <= Length (Right)
      and then (for all N in Left =>
                     Get (Left, N) = Get (Right, N)));

   function Contains
     (Container : Sequence;
      Fst       : Big_Positive;
      Lst       : Big_Natural;
      Item      : Element_Type) return Boolean
   is
     (for some I in Container =>
         Fst <= I and I <= Lst and Get (Container, I) = Item);

   function Constant_Range
     (Container : Sequence;
      Fst       : Big_Positive;
      Lst       : Big_Natural;
      Item      : Element_Type) return Boolean
   is
     (for all I in Container =>
        (if Fst <= I and I <= Lst then Get (Container, I) = Item));

   function Equal_Except
     (Left     : Sequence;
      Right    : Sequence;
      Position : Big_Positive) return Boolean
   is
     (Length (Left) = Length (Right)
      and then (for all I in Left =>
                    (if I /= Position then Get (Left, I) = Get (Right, I))));

   function Equal_Except
     (Left  : Sequence;
      Right : Sequence;
      X     : Big_Positive;
      Y     : Big_Positive) return Boolean
   is
     (Length (Left) = Length (Right)
      and then (for all I in Left =>
                    (if I /= X and I /= Y then
                        Get (Left, I) = Get (Right, I))));

   function Range_Equal
     (Left  : Sequence;
      Right : Sequence;
      Fst   : Big_Positive;
      Lst   : Big_Natural) return Boolean
   is
     (for all I in Left =>
        (if Fst <= I and I <= Lst then Get (Left, I) = Get (Right, I)));

   function Range_Shifted
     (Left   : Sequence;
      Right  : Sequence;
      Fst    : Big_Positive;
      Lst    : Big_Natural;
      Offset : Big_Integer) return Boolean
   is
     ((for all I in Left =>
           (if Fst <= I and I <= Lst then
               Get (Left, I) = Get (Right, I + Offset)))
      and
        (for all I in Right =>
             (if Fst + Offset <= I and I <= Lst + Offset then
                   Get (Left, I - Offset) = Get (Right, I))));

   function Set
     (Container : List;
      Position  : Big_Positive;
      New_Item  : Element_Type) return List
   with Subprogram_Variant => (Decreases => Position),
     Pre => Position <= Length (Container),
     Post =>
       Length (Container) = Length (Set'Result)
       and then Get (Set'Result, Position) = New_Item
       and then
         (for all I in Sequence (Container) =>
            (if I /= Position then Get (Set'Result, I) = Get (Container, I)));

   function Set
     (Container : List;
      Position  : Big_Positive;
      New_Item  : Element_Type) return List
   is
   begin
      if Position = 1 then
         return new List_Cell'(new Element_Type'(New_Item), Container.Next);
      else
         return new List_Cell'
           (Container.Value, Set (Container.Next, Position - 1, New_Item));
      end if;
   end Set;

   function Set
     (Container : Sequence;
      Position  : Big_Positive;
      New_Item  : Element_Type) return Sequence
   is (Sequence (Set (List (Container), Position, New_Item)));

   function Add (Container : List; New_Item : Element_Type) return List
   with Subprogram_Variant => (Structural => Container),
     Post =>
       Length (Container) = Length (Add'Result) - 1
       and then Get (Add'Result, Length (Add'Result)) = New_Item
       and then
         (for all I in Sequence (Container) =>
            Get (Add'Result, I) = Get (Container, I));

   function Add (Container : List; New_Item : Element_Type) return List
   is
   begin
      if Container = null then
         return new List_Cell'(new Element_Type'(New_Item), null);
      else
         return new List_Cell'
           (Container.Value, Add (Container.Next, New_Item));
      end if;
   end Add;

   function Add (Container : Sequence; New_Item : Element_Type) return Sequence
   is (Sequence (Add (List (Container), New_Item)));

   function Add
     (Container : List;
      Position  : Big_Positive;
      New_Item  : Element_Type) return List
   with Subprogram_Variant => (Decreases => Position),
     Pre  => Position <= Length (Container) + 1,
     Post =>
       Length (Container) = Length (Add'Result) - 1
       and then Get (Add'Result, Position) = New_Item
       and then
         (for all I in Sequence (Container) =>
            (if I < Position then Get (Add'Result, I) = Get (Container, I)))
       and then
         (for all I in Sequence (Container) =>
            (if I >= Position then Get (Add'Result, I + 1) = Get (Container, I)));

   function Add
     (Container : List;
      Position  : Big_Positive;
      New_Item  : Element_Type) return List
   is
   begin
      if Position = 1 then
         return new List_Cell'(new Element_Type'(New_Item), Container);
      else
         return new List_Cell'
           (Container.Value, Add (Container.Next, Position - 1, New_Item));
      end if;
   end Add;

   function Add
     (Container : Sequence;
      Position  : Big_Positive;
      New_Item  : Element_Type) return Sequence
   is (Sequence (Add (List (Container), Position, New_Item)));

   function Remove
     (Container : List;
      Position  : Big_Positive) return List
   with Subprogram_Variant => (Decreases => Position),
     Pre  => Position <= Length (Container),
     Post =>
       Length (Container) = Length (Remove'Result) + 1
       and then
         (for all I in Sequence (Container) =>
            (if I < Position then Get (Remove'Result, I) = Get (Container, I)))
       and then
         (for all I in Sequence (Container) =>
            (if I > Position then Get (Remove'Result, I - 1) = Get (Container, I)));

   function Remove
     (Container : List;
      Position  : Big_Positive) return List
   is
   begin
     if Position = 1 then
         return Container.Next;
      else
         return new List_Cell'
           (Container.Value, Remove (Container.Next, Position - 1));
      end if;
   end Remove;

   function Remove
     (Container : Sequence;
      Position  : Big_Positive) return Sequence
   is (Sequence (Remove (List (Container), Position)));

   ---------------------------
   --  Iteration Primitives --
   ---------------------------

   function Iter_First (Container : Sequence) return Big_Positive is (1);

   function Iter_Has_Element
     (Container : Sequence;
      Position  : Big_Positive) return Boolean
   is (Position <= Last (Container));

   function Iter_Next
     (Container : Sequence;
      Position  : Big_Positive) return Big_Positive
   is (Position + 1);
end Sequences;
