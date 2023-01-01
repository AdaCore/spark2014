------------------------------------------------------------------------------
--                                                                          --
--                         SPARK LIBRARY COMPONENTS                         --
--                                                                          --
--                  SPARK.CONTAINERS.FUNCTIONAL.MULTISETS                   --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--          Copyright (C) 2022-2023, Free Software Foundation, Inc.         --
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

pragma Ada_2012;

with SPARK.Containers.Parameter_Checks;
with SPARK.Big_Integers; use SPARK.Big_Integers;

private with SPARK.Containers.Functional.Maps;

generic
   type Element_Type is private;

   with function Equivalent_Elements
     (Left  : Element_Type;
      Right : Element_Type) return Boolean is "=";

   Enable_Handling_Of_Equivalence : Boolean := True;
   --  This constant should only be set to False when no particular handling
   --  of equivalence over keys is needed, that is, Equivalent_Keys defines a
   --  key uniquely.

   --  Ghost lemmas used to prove that Equivalent_Elements is an equivalence
   --  relation.

   with procedure Equivalent_Elements_Reflexive (X : Element_Type) is null
     with Ghost;
   with procedure Equivalent_Elements_Symmetric (X, Y : Element_Type) is null
     with Ghost;
   with procedure Equivalent_Elements_Transitive
        (X, Y, Z : Element_Type) is null
     with Ghost;

package SPARK.Containers.Functional.Multisets with
  SPARK_Mode => On,
  Annotate   => (GNATprove, Always_Return)
is
   type Multiset is private with
     Default_Initial_Condition => Is_Empty (Multiset),
     Iterable                  => (First       => Iter_First,
                                   Next        => Iter_Next,
                                   Has_Element => Iter_Has_Element,
                                   Element     => Iter_Element);
   --  Multisets are empty when default initialized.
   --  "For in" quantification over multisets should not be used.
   --  "For of" quantification over multisets iterates over elements.
   --  For proof, "for of" quantification is understood modulo equivalence (the
   --  range of quantification comprises all the elements that are equivalent
   --  to any element of the set), so it cannot be safely executed in
   --  general. Thus, quantified expression should only be used in disabled
   --  ghost code. This is enforced by having a special imported procedure
   --  Check_Or_Fail that will lead to link-time errors otherwise.

   ----------------------
   -- Basic Operations --
   ----------------------

   function Nb_Occurence
     (Container : Multiset;
      Element   : Element_Type) return Big_Natural with
   --  Get the number of occurence of Element in the Container

     Global => null;

   procedure Lemma_Nb_Occurence_Equivalent
     (Container            : Multiset;
      Element_1, Element_2 : Element_Type)
   --  Nb_Occurence returns the same result on all equivalent elements
   with
     Ghost,
     Global   => null,
     Annotate => (GNATprove, Automatic_Instantiation),
     Pre      => Enable_Handling_Of_Equivalence
       and then Equivalent_Elements (Element_1, Element_2),
     Post     => Nb_Occurence (Container, Element_1) =
         Nb_Occurence (Container, Element_2);

   function Contains
     (Container : Multiset;
      Element   : Element_Type) return Boolean with
   --  Returns True iff Element occurs at least one in Container

     Global   => null,
     Post     => Contains'Result = (Nb_Occurence (Container, Element) > 0),
     Annotate => (GNATprove, Inline_For_Proof);

   function Choose (Container : Multiset) return Element_Type with
   --  Returns an element of the Multiset

     Global => null,
     Pre    => not Is_Empty (Container),
     Post   => Contains (Container, Choose'Result);

   function Cardinality (Container : Multiset) return Big_Natural with
   --  The Cardinality of a Multiset is the number of elements in the Multiset
   --  taking into account the number of occurences.

     Global => null,
     Post   =>
       (for all Element of Container =>
          Nb_Occurence (Container, Element) <= Cardinality'Result);

   ------------------------
   -- Property Functions --
   ------------------------

   function "<=" (Left, Right : Multiset) return Boolean with
   --  Left <= Right if all the elements occur less in Left than in Right

   Global => null,
   Post   =>
       ("<="'Result =
         (for all Item of Left =>
            Nb_Occurence (Left, Item) <= Nb_Occurence (Right, Item)))
         and then (if "<="'Result
                   then Cardinality (Left) <= Cardinality (Right));

   function "=" (Left, Right : Multiset) return Boolean with
   --  Two Multiset are equal if and only if all the Element_Type have the same
   --  number of occurences for both Multisets (possibly 0).

     Global => null,
     Post   =>
       "="'Result =
         ((for all Element of Left =>
              Nb_Occurence (Left, Element) = Nb_Occurence (Right, Element))
          and then
            (for all Element of Right =>
                Nb_Occurence (Left, Element) = Nb_Occurence (Right, Element)))
       and then (if "="'Result
                 then (Cardinality (Left) = Cardinality (Right)));

   pragma Warnings (Off, "unused variable ""Element""");
   function Is_Empty (Container : Multiset) return Boolean with
   --  A Multiset is empty if it has no element. In other words, if the number
   --  of occurence of all the elements is 0.

     Global => null,
     Post   =>
       (Is_Empty'Result =
          (for all Element of Container => False))
         and then (Is_Empty'Result = (Cardinality (Container) = 0));
   pragma Warnings (On, "unused variable ""Element""");

   function Equal_Except
     (Left    : Multiset;
      Right   : Multiset;
      Element : Element_Type) return Boolean with
   --  Check if all the elements of Left except Element have the same number of
   --  occurences in Left and in Right and conversely.

   Ghost,
   Global => null,
   Post   =>
     Equal_Except'Result =
       ((for all E of Left =>
          (if not Equivalent_Elements (E, Element)
           then Nb_Occurence (Left, E) = Nb_Occurence (Right, E)))
          and then
            (for all E of Right =>
               (if not Equivalent_Elements (E, Element)
                then Nb_Occurence (Left, E) = Nb_Occurence (Right, E))));

   ----------------------------
   -- Construction Functions --
   ----------------------------

   --  For better efficiency of both proofs and execution, avoid using
   --  construction functions in annotations and rather use property functions.

   function Empty_Multiset return Multiset with
   --  Returns an empty Multiset

     Global => null,
     Post   => Is_Empty (Empty_Multiset'Result);

   function Add
     (Container : Multiset;
      Element   : Element_Type) return Multiset with
   --  Returns Container with the number of occurences of Element incremented
   --  by one.

     Global => null,
     Post   =>
       Contains (Add'Result, Element)
         and then Cardinality (Add'Result) = Cardinality (Container) + 1
         and then Nb_Occurence (Add'Result, Element) =
                    Nb_Occurence (Container, Element) + 1
         and then Equal_Except (Container, Add'Result, Element);

   function Add
     (Container : Multiset;
      Element   : Element_Type;
      Count     : Big_Positive) return Multiset with
   --  Returns Container with the number of occurences of Element incremented
   --  by Count.

     Global => null,
     Post   =>
       Contains (Add'Result, Element)
         and then Cardinality (Add'Result) = Cardinality (Container) + Count
         and then Nb_Occurence (Add'Result, Element) =
           Nb_Occurence (Container, Element) + Count
         and then Equal_Except (Container, Add'Result, Element);

   function Remove_All
     (Container : Multiset;
      Element   : Element_Type) return Multiset with
   --  Returns Container with no occurences of Element

     Global => null,
     Pre    => Contains (Container, Element),
     Post   => not Contains (Remove_All'Result, Element)
                 and then Cardinality (Remove_All'Result) =
                            Cardinality (Container)
                            - Nb_Occurence (Container, Element)
                 and then Equal_Except (Container, Remove_All'Result, Element);

   function Remove
     (Container : Multiset;
      Element   : Element_Type;
      Count     : Big_Positive := 1) return Multiset with
   --  Returns Container with the number of occurences of Element decremented
   --  by Count.

     Global => null,
     Pre    => Count <= Nb_Occurence (Container, Element),
     Post   =>
       Nb_Occurence (Remove'Result, Element) =
         Nb_Occurence (Container, Element) - Count
         and then Cardinality (Remove'Result) =
                    Cardinality (Container) - Count
         and then Equal_Except (Container, Remove'Result, Element);

   function Sum (Left : Multiset; Right : Multiset) return Multiset with
   --  Returns the sum of Left and Right, in which the number of occurences of
   --  an element E is the sum of its number of occurences in Left and its
   --  number of occurences in Right.

     Global => null,
     Post   =>
       Cardinality (Sum'Result) = Cardinality (Left) + Cardinality (Right)
         and Left <= Sum'Result
         and Right <= Sum'Result
         and (for all Element of Sum'Result =>
                Nb_Occurence (Sum'Result, Element) =
                  Nb_Occurence (Left, Element)
                    + Nb_Occurence (Right, Element));

   function "+"
     (Left  : Multiset;
      Right : Multiset) return Multiset renames Sum;

   function Difference
     (Left  : Multiset;
      Right : Multiset) return Multiset with
   --  Returns the difference of Left and Right, in which the number of
   --  occurences of an element E is the difference between its number of
   --  occurences in Left and its number of occurences in Right.

     Global => null,
     Post   =>
       (for all E of Left =>
          (if Nb_Occurence (Left, E) > Nb_Occurence (Right, E)
           then Contains (Difference'Result, E)))
       and then
         (for all E of Difference'Result =>
            Nb_Occurence (Difference'Result, E) =
            Max (0, Nb_Occurence (Left, E) - Nb_Occurence (Right, E)));

   function "-"
     (Left  : Multiset;
      Right : Multiset) return Multiset renames Difference;

   function Intersection
     (Left  : Multiset;
      Right : Multiset) return Multiset with
   --  Returns the intersection of Left and Right

   Global => null,
   Post   =>
       (for all Element of Left =>
         (if Contains (Right, Element)
          then Contains (Intersection'Result, Element)))
        and then
          (for all Element of Intersection'Result =>
             Nb_Occurence (Intersection'Result, Element) =
             Min (Nb_Occurence (Left, Element),
                  Nb_Occurence (Right, Element)));

   function Union
     (Left  : Multiset;
      Right : Multiset) return Multiset with
   --  Returns the union of Left and Right, i.e. the smallest Multiset
   --  containing both Left and Right.

   Global => null,
   Post   =>
     (Left <= Union'Result
      and then Right <= Union'Result
      and then
        (for all Element of Union'Result =>
           Nb_Occurence (Union'Result, Element) =
           Max (Nb_Occurence (Left, Element),
                Nb_Occurence (Right, Element))));

   ------------
   -- Lemmas --
   ------------

   procedure Lemma_Sym_Intersection
     (Left  : Multiset;
      Right : Multiset) with
   --  State that the Intersection is symmetrical

     Global => null,
     Post   => Intersection (Left, Right) = Intersection (Right, Left);

   procedure Lemma_Sym_Union
     (Left  : Multiset;
      Right : Multiset) with
   --  State that the Union is symmetrical

   Global => null,
   Post   => Union (Left, Right) = Union (Right, Left);

   procedure Lemma_Sym_Sum
     (Left  : Multiset;
      Right : Multiset) with
   --  State that the Sum is symmetrical.

     Global => null,
     Post   => Sum (Left, Right) = Sum (Right, Left);

   ---------------------------------------
   -- Iteration on Functional Multisets --
   ---------------------------------------

   --  The Iterable aspect can be used to quantify over a functional multiset.
   --  However, if it is used to create a for loop, it will not allow users to
   --  prove their loops as there is no way to speak about the elements which
   --  have or have not been traversed already in a loop invariant. The
   --  function Iterate returns an object of a type Iterable_Multiset which can
   --  be used for iteration. The cursor is a functional multiset containing
   --  all the elements which have not been traversed yet. The current element
   --  being traversed being the result of Choose on this set.

   type Iterable_Multiset is private with
     Iterable =>
       (First       => First,
        Has_Element => Has_Element,
        Next        => Next,
        Element     => Element);

   function Multiset_Logic_Equal (Left, Right : Multiset) return Boolean with
     Ghost,
     Annotate => (GNATprove, Logical_Equal);
   --  Logical equality on multisets

   function Iterate (Container : Multiset) return Iterable_Multiset with
     Global => null,
     Post   => Multiset_Logic_Equal (Get_Multiset (Iterate'Result), Container);
   --  Return an iterator over a functional multiset

   function Get_Multiset (Iterator : Iterable_Multiset) return Multiset with
     Global => null;
   --  Retrieve the multiset associated with an iterator

   function Valid_Subset
     (Iterator : Iterable_Multiset;
      Cursor   : Multiset) return Boolean
   with
     Global => null,
     Post   => (if Valid_Subset'Result then Cursor <= Get_Multiset (Iterator));
   --  Returns True on all multisets which can be reached by iterating over
   --  Container.

   function Element
     (Iterator : Iterable_Multiset; Cursor : Multiset) return Element_Type
   with
     Global   => null,
     Pre      => not Is_Empty (Cursor),
     Post     => Element'Result = Choose (Cursor),
     Annotate => (GNATprove, Inline_For_Proof);
   --  The next element to be considered for the iteration is the result of
   --  choose on Cursor.

   function First (Iterator : Iterable_Multiset) return Multiset with
     Global => null,
     Post   => Multiset_Logic_Equal (First'Result, Get_Multiset (Iterator))
       and then Valid_Subset (Iterator, First'Result);
   --  In the first iteration, the cursor is the multiset associated with
   --  Iterator.

   function Next
     (Iterator : Iterable_Multiset; Cursor : Multiset) return Multiset
   with
     Global => null,
     Pre    => Valid_Subset (Iterator, Cursor) and then not Is_Empty (Cursor),
     Post   => Valid_Subset (Iterator, Next'Result)
       and then Multiset_Logic_Equal
         (Next'Result, Remove_All (Cursor, Choose (Cursor)));
   --  At each iteration, remove the considered element from the Cursor set

   function Has_Element
     (Iterator : Iterable_Multiset;
      Cursor   : Multiset) return Boolean
   with
     Global => null,
     Post   => Has_Element'Result =
       (Valid_Subset (Iterator, Cursor) and then not Is_Empty (Cursor));
   --  Return True on non-empty sets which can be reached by iterating over
   --  Container.

   --------------------------
   -- Instantiation Checks --
   --------------------------

   --  Check that the actual parameters follow the appropriate assumptions

   function Copy_Element (Item : Element_Type) return Element_Type is (Item);
   --  Elements of containers are copied by numerous primitives in this
   --  package. This function causes GNATprove to verify that such a copy is
   --  valid (in particular, it does not break the ownership policy of SPARK,
   --  i.e. it does not contain pointers that could be used to alias mutable
   --  data).

   package Eq_Elements_Checks is new
     SPARK.Containers.Parameter_Checks.Equivalence_Checks
       (T                   => Element_Type,
        Eq                  => Equivalent_Elements,
        Param_Eq_Reflexive  => Equivalent_Elements_Reflexive,
        Param_Eq_Symmetric  => Equivalent_Elements_Symmetric,
        Param_Eq_Transitive => Equivalent_Elements_Transitive);
   --  Check that the actual parameter for Equivalent_Elements is an
   --  equivalence relation.

   --------------------------------------------------
   -- Iteration Primitives Used For Quantification --
   --------------------------------------------------

   type Private_Key is private;

   function Iter_First (Container : Multiset) return Private_Key with
     Global => null;

   function Iter_Has_Element
     (Container : Multiset;
      Key       : Private_Key) return Boolean
   with
     Global => null;

   function Iter_Next (Container : Multiset; Key : Private_Key)
                       return Private_Key
   with
     Global => null,
     Pre    => Iter_Has_Element (Container, Key);

   function Iter_Element
     (Container : Multiset;
      Key       : Private_Key) return Element_Type
   with
     Global => null,
     Pre    => Iter_Has_Element (Container, Key);
   pragma Annotate (GNATprove, Iterable_For_Proof, "Contains", Contains);

private

#if SPARK_BODY_MODE="Off"
   pragma SPARK_Mode (Off);
#end if;

   package Maps is new SPARK.Containers.Functional.Maps
     (Key_Type                   => Element_Type,
      Element_Type               => Big_Positive,
      Equivalent_Keys            => Equivalent_Elements,
      Equivalent_Keys_Reflexive  => Eq_Elements_Checks.Eq_Reflexive,
      Equivalent_Keys_Symmetric  => Eq_Elements_Checks.Eq_Symmetric,
      Equivalent_Keys_Transitive => Eq_Elements_Checks.Eq_Transitive);
   use Maps;

   type Multiset is record
      Map  : Maps.Map;
      Card : Big_Natural := 0;
   end record with
     Type_Invariant => Invariant (Map, Card);

   function Invariant (Container : Map; Card : Big_Natural) return Boolean
     with Ghost;

   ---------------------------------------
   -- Iteration on Functional Multisets --
   ---------------------------------------

   type Iterable_Multiset is record
      Map  : Maps.Iterable_Map := Iterate (Empty_Map);
      Card : Big_Natural := 0;
   end record with
     Type_Invariant => Invariant (Get_Map (Map), Card);

   function Element
     (Iterator : Iterable_Multiset;
      Cursor   : Multiset) return Element_Type
   is
     (Choose (Cursor));

   function First (Iterator : Iterable_Multiset) return Multiset is
     (Map => First (Iterator.Map), Card => Iterator.Card);

   function Get_Multiset (Iterator : Iterable_Multiset) return Multiset is
     (Map => First (Iterator.Map), Card => Iterator.Card);

   function Has_Element
     (Iterator : Iterable_Multiset;
      Cursor   : Multiset) return Boolean
   is
     (Valid_Subset (Iterator, Cursor) and then Length (Cursor.Map) > 0);

   function Iterate (Container : Multiset) return Iterable_Multiset is
     (Map => Iterate (Container.Map), Card => Container.Card);

   function Multiset_Logic_Equal (Left, Right : Multiset) return Boolean is
     (Map_Logic_Equal (Left.Map, Right.Map));

   function Valid_Subset
     (Iterator : Iterable_Multiset;
      Cursor   : Multiset) return Boolean
   is
     (Valid_Submap (Iterator.Map, Cursor.Map));

   --------------------------------------------------
   -- Iteration Primitives Used For Quantification --
   --------------------------------------------------

   type Private_Key is new Maps.Private_Key;

   function Iter_First (Container : Multiset) return Private_Key is
     (Iter_First (Container.Map));

   function Iter_Has_Element
     (Container : Multiset;
      Key       : Private_Key) return Boolean
   is
     (Iter_Has_Element (Container.Map, Key));

   function Iter_Next
     (Container : Multiset;
      Key       : Private_Key) return Private_Key
   is
     (Iter_Next (Container.Map, Key));

   function Iter_Element
     (Container : Multiset;
      Key       : Private_Key) return Element_Type
   is
     (Iter_Element (Container.Map, Key));

end SPARK.Containers.Functional.Multisets;
