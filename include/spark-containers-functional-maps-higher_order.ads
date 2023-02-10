------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--               SPARK.CONTAINERS.FUNCTIONAL.MAPS.HIGHER_ORDER              --
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
package SPARK.Containers.Functional.Maps.Higher_Order with
  SPARK_Mode,
  Annotate => (GNATprove, Always_Return)
is

   function Eq_Compatible
     (M    : Map;
      Test : not null access
        function (K : Key_Type; E : Element_Type) return Boolean)
      return Boolean
   --  Test returns the same value on equivalent keys

     with Ghost,
       Global   => null,
       Post     => Eq_Compatible'Result =
         (for all K1 of M =>
            (for all K2 of M =>
               (if Equivalent_Keys (K1, K2)
                then Test (K1, Get (M, K1)) = Test (K2, Get (M, K2))))),
       Annotate => (GNATprove, Higher_Order_Specialization),
       Annotate => (GNATprove, Inline_For_Proof);

   function Eq_Compatible
     (M     : Map;
      Value : not null access
        function (K : Key_Type; E : Element_Type) return Big_Integer)
      return Boolean
   --  Value returns the same value on equivalent keys

     with Ghost,
       Global   => null,
       Post     => Eq_Compatible'Result =
         (for all K1 of M =>
            (for all K2 of M =>
               (if Equivalent_Keys (K1, K2)
                then Value (K1, Get (M, K1)) = Value (K2, Get (M, K2))))),
       Annotate => (GNATprove, Higher_Order_Specialization),
       Annotate => (GNATprove, Inline_For_Proof);

   function Create
     (New_Length : Big_Natural;
      New_Key    : not null access function (I : Big_Positive) return Key_Type;
      New_Item   : not null access
        function (I : Big_Positive) return Element_Type)
      return Map
   --  Return a new map with New_Length associations. Each association is
   --  created by calling New_Key and New_Item.

   with
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Pre      =>
       (for all I1 in Interval'(1, New_Length) =>
          (for all I2 in Interval'(I1 + 1, New_Length) =>
             not Equivalent_Keys (New_Key (I1), New_Key (I2)))),
     Post     => Length (Create'Result) = New_Length
       and then
          (for all I in Interval'(1, New_Length) =>
             Has_Key (Create'Result, New_Key (I)))
       and then
          (for all K of Create'Result =>
             (for some I in Interval'(1, New_Length) =>
                  Equivalent_Keys (K, New_Key (I))))
       and then
          (for all I in Interval'(1, New_Length) =>
             Element_Logic_Equal
               (Get (Create'Result, New_Key (I)), New_Item (I)));

   function Transform
     (M              : Map;
      Transform_Key  : not null access function (K : Key_Type) return Key_Type;
      Transform_Item : not null access
        function (E : Element_Type) return Element_Type)
      return Map
   --  Return a new map containing a mapping per key in M. The new associations
   --  are obtained using Transform_Key and Transform_Item. Transform_Key
   --  shall not collapse keys together.

   with
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Pre      =>
       (for all K1 of M =>
          (for all K2 of M =>
             Equivalent_Keys (Transform_Key (K1), Transform_Key (K2)) =
             Equivalent_Keys (K1, K2))),
     Post     => Length (Transform'Result) = Length (M)
       and then (for all K of M =>
                   Has_Key (Transform'Result, Transform_Key (K)))
       and then
           (for all K of Transform'Result =>
              (for some L of M => Equivalent_Keys (K, Transform_Key (L))))
       and then
           (for all K of M =>
              Element_Logic_Equal
                (Get (Transform'Result, Transform_Key (K)),
                 Transform_Item (Get (M, K))));

   function Transform_Element
     (M              : Map;
      Transform_Item : not null access
        function (E : Element_Type) return Element_Type)
      return Map
   --  Return a new map containing a mapping per key in M. The new associations
   --  are obtained using Transform_Item on the associated elements.

   with
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Post     => Length (Transform_Element'Result) = Length (M)
       and then Same_Keys (M, Transform_Element'Result)
       and then
           (for all K of M =>
              Element_Logic_Equal
                (Get (Transform_Element'Result, K),
                 Transform_Item (Get (M, K))));

   function Count
     (M    : Map;
      Test : not null access
        function (K : Key_Type; E : Element_Type) return Boolean)
      return Big_Natural
   --  Count the number of mappings on which the input Test function returns
   --  True. Count can only be used with Test functions which return the same
   --  value on equivalent keys.

   with
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Pre      => Eq_Compatible (M, Test),
     Post     => Count'Result <= Length (M);

   procedure Lemma_Count_Eq
     (M1, M2 : Map;
      Test   : not null access
        function (K : Key_Type; E : Element_Type) return Boolean)
   --  Automatically instantiated lemma:
   --  Count returns the same value on maps containing the same mappings.

   with Ghost,
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Annotate => (GNATprove, Automatic_Instantiation),
     Pre      => Eq_Compatible (M1, Test) and then Keys_Included (M2, M1)
       and then Elements_Equal (M1, M2),
     Post     => Count (M1, Test) = Count (M2, Test);

   procedure Lemma_Count_Remove
     (M    : Map;
      K    : Key_Type;
      Test : not null access
        function (K : Key_Type; E : Element_Type) return Boolean)
   --  Automatically instantiated lemma:
   --  Recursive definition of Count on for any mapping in M.

   with Ghost,
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Annotate => (GNATprove, Automatic_Instantiation),
     Pre      => Has_Key (M, K) and then Eq_Compatible (M, Test),
     Post     => Count (M, Test) =
         Count (Remove (M, K), Test) +
             (if Test (K, Get (M, K)) then Big_Natural'(1) else 0);

   procedure Lemma_Count_All
     (M    : Map;
      Test : not null access
        function (K : Key_Type; E : Element_Type) return Boolean)
   --  Additional lemma:
   --  Count returns Length (M) if Test returns True on all elements of M.

   with Ghost,
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Pre      => (for all K of M => Test (K, Get (M, K))),
     Post     => Count (M, Test) = Length (M);

   procedure Lemma_Count_None
     (M    : Map;
      Test : not null access
        function (K : Key_Type; E : Element_Type) return Boolean)
   --  Additional lemma:
   --  Count returns 0 if Test returns False on all elements of M.

   with Ghost,
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Pre      => (for all K of M => not Test (K, Get (M, K))),
     Post     => Count (M, Test) = 0;

   function Filter
     (M    : Map;
      Test : not null access
        function (K : Key_Type; E : Element_Type) return Boolean)
      return Map
   --  Return a new map with all mappings of M on which the input Test function
   --  returns True. Filter can only be used with Test functions which return
   --  the same value on equivalent keys.

   with
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Pre      => Eq_Compatible (M, Test),
     Post     => Length (Filter'Result) = Count (M, Test)
       and then Elements_Equal (Filter'Result, M)
       and then (for all K of Filter'Result => Test (K, Get (M, K)))
       and then
         (for all K of M =>
            (if Test (K, Get (M, K)) then Has_Key (Filter'Result, K)));

   function Sum
     (M     : Map;
      Value : not null access
        function (K : Key_Type; E : Element_Type) return Big_Integer)
      return Big_Integer
   --  Sum the result of the Value function on all mappings of M. Sum can only
   --  be used with Value functions which return the same value on equivalent
   --  keys.

   with
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Pre      => Eq_Compatible (M, Value);

   procedure Lemma_Sum_Eq
     (M1, M2 : Map;
      Value  : not null access
        function (K : Key_Type; E : Element_Type) return Big_Integer)
   --  Automatically instantiated lemma:
   --  Sum returns the same value on maps containing the same mappings.

   with Ghost,
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Annotate => (GNATprove, Automatic_Instantiation),
     Pre      => Eq_Compatible (M1, Value) and then Keys_Included (M2, M1)
       and then Elements_Equal (M1, M2),
     Post     => Sum (M1, Value) = Sum (M2, Value);

   procedure Lemma_Sum_Remove
     (M    : Map;
      K      : Key_Type;
      Value : not null access
        function (K : Key_Type; E : Element_Type) return Big_Integer)
   --  Automatically instantiated lemma:
   --  Recursive definition of Sum for any mapping in M.

   with Ghost,
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Annotate => (GNATprove, Automatic_Instantiation),
     Pre      => Has_Key (M, K) and then Eq_Compatible (M, Value),
     Post     => Sum (M, Value) =
         Sum (Remove (M, K), Value) + Value (K, Get (M, K));

end SPARK.Containers.Functional.Maps.Higher_Order;
