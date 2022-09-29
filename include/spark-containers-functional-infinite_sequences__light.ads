------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--              SPARK.CONTAINERS.FUNCTIONAL.INFINITE_SEQUENCES              --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--          Copyright (C) 2022-2022, Free Software Foundation, Inc.         --
--                                                                          --
-- SPARK is free software;  you can  redistribute it and/or modify it under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion. SPARK is distributed in the hope that it will be useful, but WITH- --
-- OUT ANY WARRANTY;  without even the  implied warranty of MERCHANTABILITY --
-- or FITNESS FOR A PARTICULAR PURPOSE.                                     --
--                                                                          --
-- As a special exception under Section 7 of GPL version 3, you are granted --
-- additional permissions described in the GCC Runtime Library Exception,   --
-- version 3.1, as published by the Free Software Foundation.               --
--                                                                          --
-- You should have received a copy of the GNU General Public License and    --
-- a copy of the GCC Runtime Library Exception along with this program;     --
-- see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see    --
-- <http://www.gnu.org/licenses/>.                                          --
--                                                                          --
------------------------------------------------------------------------------

--  This unit is provided as a replacement for the unit
--  SPARK.Containers.Functional.Infinite_Sequences when only proof with SPARK
--  is intended. It cannot be used for execution, as all subprograms are marked
--  imported with no definition.

--  Contrary to SPARK.Containers.Functional.Infinite_Sequences, this unit does
--  not depend on System or Ada.Finalization, which makes it more convenient
--  for use in run-time units.

pragma Ada_2012;
with Ada.Containers; use Ada.Containers;
with SPARK.Big_Integers;
use SPARK.Big_Integers;

generic
   type Element_Type (<>) is private;
   with function "=" (Left, Right : Element_Type) return Boolean is <>;

package SPARK.Containers.Functional.Infinite_Sequences with
  SPARK_Mode,
  Ghost,
  Annotate => (GNATprove, Always_Return)
is

   type Sequence is private
     with Default_Initial_Condition => Length (Sequence) = 0,
     Iterable => (First       => Iter_First,
                  Has_Element => Iter_Has_Element,
                  Next        => Iter_Next,
                  Element     => Get);
   --  Sequences are empty when default initialized.
   --  Quantification over sequences can be done using the regular
   --  quantification over its range or directly on its elements with "for of".

   -----------------------
   --  Basic operations --
   -----------------------

   --  Sequences are axiomatized using Length and Get, providing respectively
   --  the length of a sequence and an accessor to its Nth element:

   function Length (Container : Sequence) return Big_Natural with
   --  Length of a sequence

     Import,
     Global => null;

   function Get
     (Container : Sequence;
      Position  : Big_Integer) return Element_Type
   --  Access the Element at position Position in Container

   with
     Import,
     Global => null,
     Pre    => Iter_Has_Element (Container, Position);

   function Last (Container : Sequence) return Big_Natural with
   --  Last index of a sequence

     Import,
     Global => null,
     Post =>
       Last'Result = Length (Container);
   pragma Annotate (GNATprove, Inline_For_Proof, Last);

   function First return Big_Positive is (1) with
   --  First index of a sequence

     Import,
     Global => null;

   ------------------------
   -- Property Functions --
   ------------------------

   function "=" (Left : Sequence; Right : Sequence) return Boolean with
   --  Extensional equality over sequences

     Import,
     Global => null,
     Post   =>
       "="'Result =
         (Length (Left) = Length (Right)
           and then (for all N in Left => Get (Left, N) = Get (Right, N)));
   pragma Annotate (GNATprove, Inline_For_Proof, "=");

   function "<" (Left : Sequence; Right : Sequence) return Boolean with
   --  Left is a strict subsequence of Right

     Import,
     Global => null,
     Post   =>
       "<"'Result =
         (Length (Left) < Length (Right)
           and then (for all N in Left => Get (Left, N) = Get (Right, N)));
   pragma Annotate (GNATprove, Inline_For_Proof, "<");

   function "<=" (Left : Sequence; Right : Sequence) return Boolean with
   --  Left is a subsequence of Right

     Import,
     Global => null,
     Post   =>
       "<="'Result =
         (Length (Left) <= Length (Right)
           and then (for all N in Left => Get (Left, N) = Get (Right, N)));
   pragma Annotate (GNATprove, Inline_For_Proof, "<=");

   function Contains
     (Container : Sequence;
      Fst       : Big_Positive;
      Lst       : Big_Natural;
      Item      : Element_Type) return Boolean
   --  Returns True if Item occurs in the range from Fst to Lst of Container

   with
     Import,
     Global => null,
     Pre    => Lst <= Last (Container),
     Post   =>
       Contains'Result =
           (for some J in Container =>
              Fst <= J and J <= Lst and Get (Container, J) = Item);
   pragma Annotate (GNATprove, Inline_For_Proof, Contains);

   function Constant_Range
     (Container : Sequence;
      Fst       : Big_Positive;
      Lst       : Big_Natural;
      Item      : Element_Type) return Boolean
   --  Returns True if every element of the range from Fst to Lst of Container
   --  is equal to Item.

   with
     Import,
     Global => null,
     Pre    => Lst <= Last (Container),
     Post   =>
       Constant_Range'Result =
           (for all J in Container =>
              (if Fst <= J and J <= Lst then Get (Container, J) = Item));
   pragma Annotate (GNATprove, Inline_For_Proof, Constant_Range);

   function Equal_Except
     (Left     : Sequence;
      Right    : Sequence;
      Position : Big_Positive) return Boolean
   --  Returns True is Left and Right are the same except at position Position

   with
     Import,
     Global => null,
     Pre    => Position <= Last (Left),
     Post   =>
       Equal_Except'Result =
         (Length (Left) = Length (Right)
           and then (for all J in Left =>
                       (if J /= Position then
                          Get (Left, J) = Get (Right, J))));
   pragma Annotate (GNATprove, Inline_For_Proof, Equal_Except);

   function Equal_Except
     (Left  : Sequence;
      Right : Sequence;
      X     : Big_Positive;
      Y     : Big_Positive) return Boolean
   --  Returns True is Left and Right are the same except at positions X and Y

   with
     Import,
     Global => null,
     Pre    => X <= Last (Left) and Y <= Last (Left),
     Post   =>
       Equal_Except'Result =
         (Length (Left) = Length (Right)
           and then (for all J in Left =>
                       (if J /= X and J /= Y then
                          Get (Left, J) = Get (Right, J))));
   pragma Annotate (GNATprove, Inline_For_Proof, Equal_Except);

   function Range_Equal
     (Left  : Sequence;
      Right : Sequence;
      Fst   : Big_Positive;
      Lst   : Big_Natural) return Boolean
   --  Returns True if the ranges from Fst to Lst contain the same elements in
   --  Left and Right.

   with
     Import,
     Global => null,
     Pre    => Lst <= Last (Left) and Lst <= Last (Right),
     Post   =>
       Range_Equal'Result =
         (for all J in Left =>
            (if Fst <= J and J <= Lst then Get (Left, J) = Get (Right, J)));
   pragma Annotate (GNATprove, Inline_For_Proof, Range_Equal);

   function Range_Shifted
     (Left   : Sequence;
      Right  : Sequence;
      Fst    : Big_Positive;
      Lst    : Big_Natural;
      Offset : Big_Integer) return Boolean
   --  Returns True if the range from Fst to Lst in Left contains the same
   --  elements as the range from Fst + Offset to Lst + Offset in Right.

   with
     Import,
     Global => null,
     Pre    =>
       Lst <= Last (Left)
         and then
           (if Fst <= Lst then
              Offset + Fst >= 1 and Offset + Lst <= Length (Right)),
     Post   =>
       Range_Shifted'Result =
         ((for all J in Left =>
             (if Fst <= J and J <= Lst then
                Get (Left, J) = Get (Right, J + Offset)))
          and
            (for all J in Right =>
               (if Fst + Offset <= J and J <= Lst + Offset then
                  Get (Left, J - Offset) = Get (Right, J))));
   pragma Annotate (GNATprove, Inline_For_Proof, Range_Shifted);

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
     Import,
     Global => null,
     Pre    => Position <= Last (Container),
     Post   =>
       Get (Set'Result, Position) = New_Item
         and then Equal_Except (Container, Set'Result, Position);

   function Add (Container : Sequence; New_Item : Element_Type) return Sequence
   --  Returns a new sequence which contains the same elements as Container
   --  plus New_Item at the end.

   with
     Import,
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

     Import,
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
      Position : Big_Positive) return Sequence
   --  Returns a new sequence which contains the same elements as Container
   --  except that the element at position Position has been removed.

   with
     Import,
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

   function Empty_Sequence return Sequence with
   --  Return an empty Sequence

     Import,
     Global => null,
     Post   => Length (Empty_Sequence'Result) = 0;

   ---------------------------
   --  Iteration Primitives --
   ---------------------------

   function Iter_First (Container : Sequence) return Big_Integer with
     Import,
     Global => null,
     Post   => Iter_First'Result = 1;

   function Iter_Has_Element
     (Container : Sequence;
      Position  : Big_Integer) return Boolean
   with
     Import,
     Global => null,
     Post   => Iter_Has_Element'Result =
                   In_Range (Position, 1, Length (Container));
   pragma Annotate (GNATprove, Inline_For_Proof, Iter_Has_Element);

   function Iter_Next
     (Container : Sequence;
      Position  : Big_Integer) return Big_Integer
   with
     Import,
     Global => null,
     Pre    => Iter_Has_Element (Container, Position),
     Post   => Iter_Next'Result = Position + 1;

private
   pragma SPARK_Mode (Off);

   type Sequence is null record;

end SPARK.Containers.Functional.Infinite_Sequences;
