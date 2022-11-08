------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--                    SPARK.CONTAINERS.FUNCTIONAL.SETS                      --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--          Copyright (C) 2016-2022, Free Software Foundation, Inc.         --
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
--  SPARK.Containers.Functional.Sets when only proof with SPARK is
--  intended. It cannot be used for execution, as all subprograms are marked
--  imported with no definition.

--  Contrary to SPARK.Containers.Functional.Sets, this unit does not
--  depend on System or Ada.Finalization, which makes it more convenient for
--  use in run-time units.

pragma Ada_2012;

with SPARK.Big_Integers; use SPARK.Big_Integers;

generic
   type Element_Type (<>) is private;

   with function Equivalent_Elements
     (Left  : Element_Type;
      Right : Element_Type) return Boolean is "=";

   Enable_Handling_Of_Equivalence : Boolean := True;
   --  This constant should only be set to False when no particular handling
   --  of equivalence over elements is needed, that is, Equivalent_Elements
   --  defines an element uniquely.

package SPARK.Containers.Functional.Sets with
  SPARK_Mode,
  Ghost,
  Annotate => (GNATprove, Always_Return)
is

   type Set is private with
     Default_Initial_Condition => Is_Empty (Set),
     Iterable                  => (First       => Iter_First,
                                   Next        => Iter_Next,
                                   Has_Element => Iter_Has_Element,
                                   Element     => Iter_Element);
   --  Sets are empty when default initialized.
   --  "For in" quantification over sets should not be used.
   --  "For of" quantification over sets iterates over elements.
   --  Note that, for proof, "for of" quantification is understood modulo
   --  equivalence (the range of quantification comprises all the elements that
   --  are equivalent to any element of the set).

   -----------------------
   --  Basic operations --
   -----------------------

   --  Sets are axiomatized using Contains, which encodes whether an element is
   --  contained in a set. The length of a set is also added to protect Add
   --  against overflows but it is not actually modeled.

   function Contains (Container : Set; Item : Element_Type) return Boolean with
     Global => null;
   --  Return True if Item is contained in Container

   procedure Lemma_Contains_Equivalent
     (Container : Set;
      Item      : Element_Type)
   --  Contains returns the same result on all equivalent elements
   with
     Ghost,
     Global => null,
     Annotate => (GNATprove, Automatic_Instantiation),
     Pre  => Enable_Handling_Of_Equivalence
       and then not Contains (Container, Item),
     Post => (for all E of Container => not Equivalent_Elements (Item, E));

   function Choose (Container : Set) return Element_Type with
   --  Return an arbitrary element in Container

     Global => null,
     Pre    => not Is_Empty (Container),
     Post   => Contains (Container, Choose'Result);

   function Length (Container : Set) return Big_Natural with
     Global => null;
   --  Return the number of elements in Container

   ------------------------
   -- Property Functions --
   ------------------------

   function "<=" (Left : Set; Right : Set) return Boolean with
   --  Set inclusion

     Global => null,
     Post   => "<="'Result = (for all Item of Left => Contains (Right, Item));

   function "=" (Left : Set; Right : Set) return Boolean with
   --  Extensional equality over sets

     Global => null,
     Post   => "="'Result = (Left <= Right and Right <= Left);

   pragma Warnings (Off, "unused variable ""Item""");
   function Is_Empty (Container : Set) return Boolean with
   --  A set is empty if it contains no element

     Global => null,
     Post   =>
       Is_Empty'Result = (for all Item of Container => False)
         and Is_Empty'Result = (Length (Container) = 0);
   pragma Warnings (On, "unused variable ""Item""");

   function Included_Except
     (Left  : Set;
      Right : Set;
      Item  : Element_Type) return Boolean
   --  Return True if Left contains only elements of Right except possibly
   --  Item.

   with
     Global => null,
     Post   =>
       Included_Except'Result =
         (for all E of Left =>
           Contains (Right, E) or Equivalent_Elements (E, Item));

   function Includes_Intersection
     (Container : Set;
      Left      : Set;
      Right     : Set) return Boolean
   with
   --  Return True if every element of the intersection of Left and Right is
   --  in Container.

     Global => null,
     Post   =>
       Includes_Intersection'Result =
         (for all Item of Left =>
           (if Contains (Right, Item) then Contains (Container, Item)));

   function Included_In_Union
     (Container : Set;
      Left      : Set;
      Right     : Set) return Boolean
   with
   --  Return True if every element of Container is the union of Left and Right

     Global => null,
     Post   =>
       Included_In_Union'Result =
         (for all Item of Container =>
           Contains (Left, Item) or Contains (Right, Item));

   function Is_Singleton
     (Container : Set;
      New_Item  : Element_Type) return Boolean
   with
   --  Return True Container only contains New_Item

     Global => null,
     Post   =>
       Is_Singleton'Result =
         (for all Item of Container => Equivalent_Elements (Item, New_Item));

   function Not_In_Both
     (Container : Set;
      Left      : Set;
      Right     : Set) return Boolean
   --  Return True if there are no elements in Container that are in Left and
   --  Right.

   with
     Global => null,
     Post   =>
       Not_In_Both'Result =
         (for all Item of Container =>
            not Contains (Left, Item) or not Contains (Right, Item));

   function No_Overlap (Left : Set; Right : Set) return Boolean with
   --  Return True if there are no equivalent elements in Left and Right

     Global => null,
     Post   =>
       No_Overlap'Result =
         (for all Item of Left => not Contains (Right, Item));

   function Num_Overlaps (Left : Set; Right : Set) return Big_Natural with
   --  Number of elements that are both in Left and Right

     Global => null,
     Post   =>
       Num_Overlaps'Result = Length (Intersection (Left, Right))
         and (if Left <= Right then Num_Overlaps'Result = Length (Left)
              else Num_Overlaps'Result < Length (Left))
         and (if Right <= Left then Num_Overlaps'Result = Length (Right)
              else Num_Overlaps'Result < Length (Right))
         and (Num_Overlaps'Result = 0) = No_Overlap (Left, Right);

   ----------------------------
   -- Construction Functions --
   ----------------------------

   --  For better efficiency of both proofs and execution, avoid using
   --  construction functions in annotations and rather use property functions.

   function Add (Container : Set; Item : Element_Type) return Set with
   --  Return a new set containing all the elements of Container plus E

     Global => null,
     Pre    => not Contains (Container, Item),
     Post   =>
       Length (Add'Result) = Length (Container) + 1
         and Contains (Add'Result, Item)
         and Container <= Add'Result
         and Included_Except (Add'Result, Container, Item);

   function Empty_Set return Set with
   --  Return a new empty set

     Global => null,
     Post   => Is_Empty (Empty_Set'Result);

   function Remove (Container : Set; Item : Element_Type) return Set with
   --  Return a new set containing all the elements of Container except E

     Global => null,
     Pre    => Contains (Container, Item),
     Post   =>
       Length (Remove'Result) = Length (Container) - 1
         and not Contains (Remove'Result, Item)
         and Remove'Result <= Container
         and Included_Except (Container, Remove'Result, Item);

   function Intersection (Left : Set; Right : Set) return Set with
   --  Returns the intersection of Left and Right

     Global => null,
     Post   =>
       Intersection'Result <= Left
         and Intersection'Result <= Right
         and Includes_Intersection (Intersection'Result, Left, Right);

   function Union (Left : Set; Right : Set) return Set with
   --  Returns the union of Left and Right

     Global => null,
     Post   =>
       Length (Union'Result) =
         Length (Left) - Num_Overlaps (Left, Right) + Length (Right)
           and Left <= Union'Result
           and Right <= Union'Result
           and Included_In_Union (Union'Result, Left, Right);

   function Copy_Element (Item : Element_Type) return Element_Type is (Item);
   --  Elements of containers are copied by numerous primitives in this
   --  package. This function causes GNATprove to verify that such a copy is
   --  valid (in particular, it does not break the ownership policy of SPARK,
   --  i.e. it does not contain pointers that could be used to alias mutable
   --  data).

   ----------------------------------
   -- Iteration on Functional Sets --
   ----------------------------------

   --  The Iterable aspect can be used to quantify over a functional set.
   --  However, if it is used to create a for loop, it will not allow users to
   --  prove their loops as there is no way to speak about the elements which
   --  have or have not been traversed already in a loop invariant. The
   --  function Iterate returns an object of a type Iterable_Set which can be
   --  used for iteration. The cursor is a functional set containing all the
   --  elements which have not been traversed yet. The current element being
   --  traversed being the result of Choose on this set.

   type Iterable_Set is private with
     Iterable =>
       (First       => First,
        Has_Element => Has_Element,
        Next        => Next,
        Element     => Element);

   function Set_Logic_Equal (Left, Right : Set) return Boolean with
     Ghost,
     Annotate => (GNATprove, Logical_Equal);
   --  Logical equality on sets

   function Iterate (Container : Set) return Iterable_Set with
     Global => null,
     Post   => Set_Logic_Equal (Get_Set (Iterate'Result), Container);
   --  Return an iterator over a functional set

   function Get_Set (Iterator : Iterable_Set) return Set with
     Global => null;
   --  Retrieve the set associated with an iterator

   function Valid_Subset
     (Iterator : Iterable_Set;
      Cursor   : Set) return Boolean
   with
     Global => null,
     Post   => (if Valid_Subset'Result then Cursor <= Get_Set (Iterator));
   --  Return True on all sets which can be reached by iterating over
   --  Container.

   function Element (Iterator : Iterable_Set; Cursor : Set) return Element_Type
   with
     Global => null,
     Pre    => not Is_Empty (Cursor),
     Post   => Element'Result = Choose (Cursor);
   --  The next element to be considered for the iteration is the result of
   --  choose on Cursor.

   function First (Iterator : Iterable_Set) return Set with
     Global => null,
     Post   => Set_Logic_Equal (First'Result, Get_Set (Iterator))
       and then Valid_Subset (Iterator, First'Result);
   --  In the first iteration, the cursor is the set associated with Iterator

   function Next (Iterator : Iterable_Set; Cursor : Set) return Set with
     Global => null,
     Pre    => Valid_Subset (Iterator, Cursor) and then not Is_Empty (Cursor),
     Post   => Valid_Subset (Iterator, Next'Result)
       and then Set_Logic_Equal
         (Next'Result, Remove (Cursor, Choose (Cursor)));
   --  At each iteration, remove the considered element from the Cursor set

   function Has_Element
     (Iterator : Iterable_Set;
      Cursor   : Set) return Boolean
   with
     Global => null,
     Post   => Has_Element'Result =
       (Valid_Subset (Iterator, Cursor) and then not Is_Empty (Cursor));
   --  Return True on non-empty sets which can be reached by iterating over
   --  Container.

   --------------------------------------------------
   -- Iteration Primitives Used For Quantification --
   --------------------------------------------------

   type Private_Key is private;

   function Iter_First (Container : Set) return Private_Key with
     Global => null;

   function Iter_Has_Element
     (Container : Set;
      Key       : Private_Key) return Boolean
   with
     Global => null;

   function Iter_Next
     (Container : Set;
      Key       : Private_Key) return Private_Key
   with
     Global => null,
     Pre    => Iter_Has_Element (Container, Key);

   function Iter_Element
     (Container : Set;
      Key       : Private_Key) return Element_Type
   with
     Global => null,
     Pre    => Iter_Has_Element (Container, Key);
   pragma Annotate (GNATprove, Iterable_For_Proof, "Contains", Contains);

private

   pragma SPARK_Mode (Off);

   type Set is null record;
   type Iterable_Set is null record;
   type Private_Key is null record;

   --------------------------------------------------
   -- Iteration Primitives Used For Quantification --
   --------------------------------------------------

   function Iter_Element
     (Container : Set;
      Key       : Private_Key) return Element_Type
   is
     (raise Program_Error);

   function Iter_First (Container : Set) return Private_Key is
     (raise Program_Error);

   function Iter_Has_Element
     (Container : Set;
      Key       : Private_Key) return Boolean
   is
     (raise Program_Error);

   function Iter_Next
     (Container : Set;
      Key       : Private_Key) return Private_Key
   is
     (raise Program_Error);

   ----------------------------------
   -- Iteration on Functional Sets --
   ----------------------------------

   function Element
     (Iterator : Iterable_Set;
      Cursor   : Set) return Element_Type
   is
     (raise Program_Error);

   function First (Iterator : Iterable_Set) return Set is
     (raise Program_Error);

   function Get_Set (Iterator : Iterable_Set) return Set is
     (raise Program_Error);

   function Has_Element
     (Iterator : Iterable_Set;
      Cursor   : Set) return Boolean
   is
     (raise Program_Error);

   function Iterate (Container : Set) return Iterable_Set is
     (raise Program_Error);

   function Next (Iterator : Iterable_Set; Cursor : Set) return Set is
     (raise Program_Error);

   function Set_Logic_Equal (Left, Right : Set) return Boolean is
     (raise Program_Error);

   function Valid_Subset
     (Iterator : Iterable_Set;
      Cursor   : Set) return Boolean
   is
     (raise Program_Error);

end SPARK.Containers.Functional.Sets;
