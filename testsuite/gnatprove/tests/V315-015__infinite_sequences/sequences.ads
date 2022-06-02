
with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;

generic
   type Element_Type (<>) is private;
package Sequences with SPARK_Mode,
  Annotate => (GNATprove, Always_Return)
is

   type Sequence is private
     with Default_Initial_Condition => Length (Sequence) = 0,
     Iterable => (First       => Iter_First,
                  Has_Element => Iter_Has_Element,
                  Next        => Iter_Next,
                  Element     => Get);
   --  Sequences are empty when default initialized.

   -----------------------
   --  Basic operations --
   -----------------------

   --  Sequences are axiomatized using Length and Get, providing respectively
   --  the length of a sequence and an accessor to its Nth element:

   function Length (Container : Sequence) return Big_Natural with
   --  Length of a sequence

     Global => null;

   function Get
     (Container : Sequence;
      Position  : Big_Positive) return Element_Type
   --  Access the Element at position Position in Container

   with
     Global => null,
     Pre    => Position <= Last (Container);

   function Last (Container : Sequence) return Big_Natural with
   --  Last index of a sequence

     Global => null,
     Post => Last'Result = Length (Container);
   pragma Annotate (GNATprove, Inline_For_Proof, Last);

   function First return Big_Positive is (1) with
     Global => null;
   --  First index of a sequence

   ------------------------
   -- Property Functions --
   ------------------------

   function "=" (Left : Sequence; Right : Sequence) return Boolean with
   --  Extensional equality over sequences

     Global => null,
     Post   =>
       "="'Result =
         (Length (Left) = Length (Right)
           and then (for all N in Left => Get (Left, N) = Get (Right, N)));

   function "<" (Left : Sequence; Right : Sequence) return Boolean with
   --  Left is a strict subsequence of Right

     Global => null,
     Post   =>
       "<"'Result =
         (Length (Left) < Length (Right)
           and then (for all N in Left =>
                      Get (Left, N) = Get (Right, N)));

   function "<=" (Left : Sequence; Right : Sequence) return Boolean with
   --  Left is a subsequence of Right

     Global => null,
     Post   =>
       "<="'Result =
         (Length (Left) <= Length (Right)
           and then (for all N in Left =>
                      Get (Left, N) = Get (Right, N)));

   function Contains
     (Container : Sequence;
      Fst       : Big_Positive;
      Lst       : Big_Natural;
      Item      : Element_Type) return Boolean
   --  Returns True if Item occurs in the range from Fst to Lst of Container

   with
     Global => null,
     Pre    => Lst <= Last (Container),
     Post   =>
       Contains'Result =
         (for some I in Container =>
            Fst <= I and I <= Lst and Get (Container, I) = Item);

   function Constant_Range
     (Container : Sequence;
      Fst       : Big_Positive;
      Lst       : Big_Natural;
      Item      : Element_Type) return Boolean
   --  Returns True if every element of the range from Fst to Lst of Container
   --  is equal to Item.

   with
     Global => null,
     Pre    => Lst <= Last (Container),
     Post   =>
       Constant_Range'Result =
         (for all I in Container =>
            (if Fst <= I and I <= Lst then Get (Container, I) = Item));

   function Equal_Except
     (Left     : Sequence;
      Right    : Sequence;
      Position : Big_Positive) return Boolean
   --  Returns True is Left and Right are the same except at position Position

   with
     Global => null,
     Pre    => Position <= Last (Left),
     Post   =>
       Equal_Except'Result =
         (Length (Left) = Length (Right)
           and then (for all I in Left =>
                      (if I /= Position then Get (Left, I) = Get (Right, I))));

   function Equal_Except
     (Left  : Sequence;
      Right : Sequence;
      X     : Big_Positive;
      Y     : Big_Positive) return Boolean
   --  Returns True is Left and Right are the same except at positions X and Y

   with
     Global => null,
     Pre    => X <= Last (Left) and Y <= Last (Left),
     Post   =>
       Equal_Except'Result =
         (Length (Left) = Length (Right)
           and then (for all I in Left =>
                      (if I /= X and I /= Y then
                          Get (Left, I) = Get (Right, I))));

   function Range_Equal
     (Left  : Sequence;
      Right : Sequence;
      Fst   : Big_Positive;
      Lst   : Big_Natural) return Boolean
   --  Returns True if the ranges from Fst to Lst contain the same elements in
   --  Left and Right.

   with
     Global => null,
     Pre    => Lst <= Last (Left) and Lst <= Last (Right),
     Post   =>
       Range_Equal'Result =
         (for all I in Left =>
            (if Fst <= I and I <= Lst then Get (Left, I) = Get (Right, I)));

   function Range_Shifted
     (Left   : Sequence;
      Right  : Sequence;
      Fst    : Big_Positive;
      Lst    : Big_Natural;
      Offset : Big_Integer) return Boolean
   --  Returns True if the range from Fst to Lst in Left contains the same
   --  elements as the range from Fst + Offset to Lst + Offset in Right.

   with
     Global => null,
     Pre    =>
       Lst <= Last (Left)
         and then
           (if Fst <= Lst then
              1 - Fst <= Offset and Offset <= Length (Right) - Lst),
     Post   =>
       Range_Shifted'Result =
         ((for all I in Left =>
             (if Fst <= I and I <= Lst then
                Get (Left, I) = Get (Right, I + Offset)))
          and
            (for all I in Right =>
               (if Fst + Offset <= I and I <= Lst + Offset then
                    Get (Left, I - Offset) = Get (Right, I))));

   ----------------------------
   -- Construction Functions --
   ----------------------------

   --  For better efficiency of both proofs and execution, avoid using
   --  construction functions in annotations and rather use property functions.

   function Set
     (Container : Sequence;
      Position  : Big_Positive;
      New_Item  : Element_Type) return Sequence
   --  Returns a new sequence which contains the same elements as Container
   --  except for the one at position Position which is replaced by New_Item.

   with
     Global => null,
     Pre    => Position <= Last (Container),
     Post   =>
       Get (Set'Result, Position) = New_Item
         and then Equal_Except (Container, Set'Result, Position);

   function Add (Container : Sequence; New_Item : Element_Type) return Sequence
   --  Returns a new sequence which contains the same elements as Container
   --  plus New_Item at the end.

   with
     Global => null,
     Post   =>
       Length (Add'Result) = Length (Container) + 1
         and then Get (Add'Result, Last (Add'Result)) = New_Item
         and then Container <= Add'Result;

   function Add
     (Container : Sequence;
      Position  : Big_Positive;
      New_Item  : Element_Type) return Sequence
   with
   --  Returns a new sequence which contains the same elements as Container
   --  except that New_Item has been inserted at position Position.

     Global => null,
     Pre    => Position <= Last (Container) + 1,
     Post   =>
       Length (Add'Result) = Length (Container) + 1
         and then Get (Add'Result, Position) = New_Item
         and then Range_Equal
                    (Left  => Container,
                     Right => Add'Result,
                     Fst   => 1,
                     Lst   => Position - 1)
         and then Range_Shifted
                    (Left   => Container,
                     Right  => Add'Result,
                     Fst    => Position,
                     Lst    => Last (Container),
                     Offset => 1);

   function Remove
     (Container : Sequence;
      Position  : Big_Positive) return Sequence
   --  Returns a new sequence which contains the same elements as Container
   --  except that the element at position Position has been removed.

   with
     Global => null,
     Pre    => Position <= Last (Container),
     Post   =>
       Length (Remove'Result) = Length (Container) - 1
         and then Range_Equal
                    (Left  => Container,
                     Right => Remove'Result,
                     Fst   => 1,
                     Lst   => Position - 1)
         and then Range_Shifted
                    (Left   => Remove'Result,
                     Right  => Container,
                     Fst    => Position,
                     Lst    => Last (Remove'Result),
                     Offset => 1);

   function Copy_Element (Item : Element_Type) return Element_Type is (Item);
   --  Elements of containers are copied by numerous primitives in this
   --  package. This function causes GNATprove to verify that such a copy is
   --  valid (in particular, it does not break the ownership policy of SPARK,
   --  i.e. it does not contain pointers that could be used to alias mutable
   --  data).

   ---------------------------
   --  Iteration Primitives --
   ---------------------------

   function Iter_First (Container : Sequence) return Big_Positive with
     Global => null;

   function Iter_Has_Element
     (Container : Sequence;
      Position  : Big_Positive) return Boolean
   with
     Global => null,
     Post   =>
       Iter_Has_Element'Result = (Position <= Last (Container));
   pragma Annotate (GNATprove, Inline_For_Proof, Iter_Has_Element);

   function Iter_Next
     (Container : Sequence;
      Position  : Big_Positive) return Big_Positive
   with
     Global => null,
     Pre    => Iter_Has_Element (Container, Position);

private
   type Element_Access is access constant Element_Type;
   type List_Cell;
   type List is access constant List_Cell;
   type List_Cell is record
      Value : not null Element_Access;
      Next  : List;
   end record;
   type Sequence is new List;
end Sequences;
