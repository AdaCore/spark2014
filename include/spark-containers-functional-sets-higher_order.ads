------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--               SPARK.CONTAINERS.FUNCTIONAL.SETS.HIGHER_ORDER              --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--          Copyright (C) 2023-2023, Free Software Foundation, Inc.         --
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
with SPARK.Big_Intervals; use SPARK.Big_Intervals;

generic
package SPARK.Containers.Functional.Sets.Higher_Order with
  SPARK_Mode,
  Annotate => (GNATprove, Always_Return)
is

   function Eq_Compatible
     (S    : Set;
      Test : not null access function (E : Element_Type) return Boolean)
      return Boolean
   --  Test returns the same value on equivalent elements

     with Ghost,
       Global   => null,
       Post     => Eq_Compatible'Result =
         (for all E1 of S =>
            (for all E2 of S =>
               (if Equivalent_Elements (E1, E2) then Test (E1) = Test (E2)))),
       Annotate => (GNATprove, Higher_Order_Specialization),
       Annotate => (GNATprove, Inline_For_Proof);

   function Eq_Compatible
     (S     : Set;
      Value : not null access function (E : Element_Type) return Big_Integer)
      return Boolean
   --  Value returns the same value on equivalent keys

     with Ghost,
       Global   => null,
       Post     => Eq_Compatible'Result =
         (for all E1 of S =>
            (for all E2 of S =>
               (if Equivalent_Elements (E1, E2)
                then Value (E1) = Value (E2)))),
       Annotate => (GNATprove, Higher_Order_Specialization),
       Annotate => (GNATprove, Inline_For_Proof);

   function Create_Distinct
     (New_Length : Big_Natural;
      New_Item   : not null access
        function (I : Big_Positive) return Element_Type)
      return Set
   --  Return a new set created by calling New_Item New_Length times.
   --  Create_Distinct can only be used on New_Item functions which create
   --  distinct elements for all integers up to New_Length. Use Create
   --  otherwise.

   with
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Pre      =>
       (for all I1 in Interval'(1, New_Length) =>
          (for all I2 in Interval'(I1 + 1, New_Length) =>
             not Equivalent_Elements (New_Item (I1), New_Item (I2)))),
     Post     => Length (Create_Distinct'Result) = New_Length
       and then
          (for all I in Interval'(1, New_Length) =>
             Contains (Create_Distinct'Result, New_Item (I)))
       and then
          (for all E of Create_Distinct'Result =>
             (for some I in Interval'(1, New_Length) =>
                  Equivalent_Elements (E, New_Item (I))));

   function Create
     (New_Length : Big_Natural;
      New_Item   : not null access
        function (I : Big_Positive) return Element_Type)
      return Set
   --  Return a new set created by calling New_Item New_Length times. Create
   --  is less efficient than Create_Distinct as it needs to check for
   --  duplicated values before inclusion.

   with
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Post     => Length (Create'Result) <= New_Length
       and then
          (for all I in Interval'(1, New_Length) =>
             Contains (Create'Result, New_Item (I)))
       and then
          (for all E of Create'Result =>
             (for some I in Interval'(1, New_Length) =>
                  Equivalent_Elements (E, New_Item (I))));

   procedure Lemma_Create_Distinct
     (New_Length : Big_Natural;
      New_Item   : not null access
        function (I : Big_Positive) return Element_Type)
   --  Additional lemma:
   --  The result of Create contains New_Length elements if New_Item never
   --  creates equivalent values on integers up to New_Length.

   with Ghost,
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Pre      =>
       (for all I1 in Interval'(1, New_Length) =>
          (for all I2 in Interval'(I1 + 1, New_Length) =>
             not Equivalent_Elements (New_Item (I1), New_Item (I2)))),
     Post     => Length (Create (New_Length, New_Item)) = New_Length;

   function Transform_Distinct
     (S              : Set;
      Transform_Item : not null access
        function (E : Element_Type) return Element_Type)
      return Set
   --  Return a new set containing elements obtained by applying Transform_Item
   --  to elements of S. Transform_Distinct can only be used with
   --  Transform_Item functions which never collapse elements. Use Transform
   --  otherwise.

   with
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Pre      =>
       (for all E1 of S =>
          (for all E2 of S =>
             Equivalent_Elements (Transform_Item (E1), Transform_Item (E2)) =
             Equivalent_Elements (E1, E2))),
     Post     => Length (Transform_Distinct'Result) = Length (S)
       and then (for all E of S =>
                   Contains (Transform_Distinct'Result, Transform_Item (E)))
       and then
           (for all E of Transform_Distinct'Result =>
              (for some F of S =>
                 Equivalent_Elements (E, Transform_Item (F))));

   function Transform
     (S              : Set;
      Transform_Item : not null access
        function (E : Element_Type) return Element_Type)
      return Set
   --  Return a new set containing elements obtained by applying Transform_Item
   --  to elements of S. Transform can only be used with Transform_Item
   --  functions which return the same equivalent value on equivalent elements.
   --  Transform is less efficient than Transform_Distinct as it needs to check
   --  for duplicated values before inclusion.

   with
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Pre      =>
       (for all E1 of S =>
          (for all E2 of S =>
             (if Equivalent_Elements (E1, E2)
              then Equivalent_Elements
                (Transform_Item (E1), Transform_Item (E2))))),
     Post     => Length (Transform'Result) <= Length (S)
       and then (for all E of S =>
                   Contains (Transform'Result, Transform_Item (E)))
       and then
           (for all E of Transform'Result =>
              (for some F of S =>
                 Equivalent_Elements (E, Transform_Item (F))));

   procedure Lemma_Transform_Distinct
     (S              : Set;
      Transform_Item : not null access
        function (E : Element_Type) return Element_Type)
   --  Additional lemma:
   --  The result of Transform contains New_Length elements if Transform_Item
   --  never collapses elements of S.

   with Ghost,
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Pre      =>
       (for all E1 of S =>
          (for all E2 of S =>
             Equivalent_Elements (Transform_Item (E1), Transform_Item (E2)) =
             Equivalent_Elements (E1, E2))),
     Post     => Length (Transform (S, Transform_Item)) = Length (S);

   function Count
     (S    : Set;
      Test : not null access function (E : Element_Type) return Boolean)
      return Big_Natural
   --  Count the number of elements on which the input Test function returns
   --  True. Count can only be used with Test functions which return the same
   --  value on equivalent elements.

   with
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Pre      => Eq_Compatible (S, Test),
     Post     => Count'Result <= Length (S);

   procedure Lemma_Count_Eq
     (S1, S2 : Set;
      Test   : not null access function (E : Element_Type) return Boolean)
   --  Automatically instantiated lemma:
   --  Count returns the same value on sets containing the same elements.

   with Ghost,
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Annotate => (GNATprove, Automatic_Instantiation),
     Pre      => Eq_Compatible (S1, Test) and then S1 = S2,
     Post     => Count (S1, Test) = Count (S2, Test);

   procedure Lemma_Count_Remove
     (S    : Set;
      E    : Element_Type;
      Test : not null access function (E : Element_Type) return Boolean)
   --  Automatically instantiated lemma:
   --  Recursive definition of Count on for any element in S.

   with Ghost,
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Annotate => (GNATprove, Automatic_Instantiation),
     Pre      => Contains (S, E) and then Eq_Compatible (S, Test),
     Post     => Count (S, Test) =
         Count (Remove (S, E), Test) +
             (if Test (E) then Big_Natural'(1) else 0);

   procedure Lemma_Count_All
     (S    : Set;
      Test : not null access function (E : Element_Type) return Boolean)
   --  Additional lemma:
   --  Count returns Length (S) if Test returns True on all elements of S.

   with Ghost,
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Pre      => (for all E of S => Test (E)),
     Post     => Count (S, Test) = Length (S);

   procedure Lemma_Count_None
     (S    : Set;
      Test : not null access function (E : Element_Type) return Boolean)
   --  Additional lemma:
   --  Count returns 0 if Test returns False on all elements of S.

   with Ghost,
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Pre      => (for all E of S => not Test (E)),
     Post     => Count (S, Test) = 0;

   function Filter
     (S    : Set;
      Test : not null access function (E : Element_Type) return Boolean)
      return Set
   --  Return a new set with all elements of S on which the input Test function
   --  returns True. Filter can only be used with Test functions which return
   --  the same value on equivalent elements.

   with
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Pre      => Eq_Compatible (S, Test),
     Post     => Length (Filter'Result) = Count (S, Test)
       and then Filter'Result <= S
       and then (for all E of Filter'Result => Test (E))
       and then
         (for all E of S => (if Test (E) then Contains (Filter'Result, E)));

   function Sum
     (S     : Set;
      Value : not null access function (E : Element_Type) return Big_Integer)
      return Big_Integer
   --  Sum the result of the Value function on all elements of S. Sum can only
   --  be used with Value functions which return the same value on equivalent
   --  elements.

   with
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Pre      => Eq_Compatible (S, Value);

   procedure Lemma_Sum_Eq
     (S1, S2 : Set;
      Value  : not null access function (E : Element_Type) return Big_Integer)
   --  Automatically instantiated lemma:
   --  Sum returns the same value on sets containing the same elements.

   with Ghost,
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Annotate => (GNATprove, Automatic_Instantiation),
     Pre      => Eq_Compatible (S1, Value) and then S1 = S2,
     Post     => Sum (S1, Value) = Sum (S2, Value);

   procedure Lemma_Sum_Remove
     (S     : Set;
      E     : Element_Type;
      Value : not null access function (E : Element_Type) return Big_Integer)
   --  Automatically instantiated lemma:
   --  Recursive definition of Sum for any element of S.

   with Ghost,
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Annotate => (GNATprove, Automatic_Instantiation),
     Pre      => Contains (S, E) and then Eq_Compatible (S, Value),
     Post     => Sum (S, Value) = Sum (Remove (S, E), Value) + Value (E);

end SPARK.Containers.Functional.Sets.Higher_Order;
