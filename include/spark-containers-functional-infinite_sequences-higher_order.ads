------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--        SPARK.CONTAINERS.FUNCTIONAL.INFINITE_SEQUENCES.HIGHER_ORDER       --
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

pragma Ada_2022;
with SPARK.Big_Intervals; use SPARK.Big_Intervals;

generic
package SPARK.Containers.Functional.Infinite_Sequences.Higher_Order with
  SPARK_Mode,
  Annotate => (GNATprove, Always_Return)
is

   function Create
     (New_Length : Big_Natural;
      New_Item   : not null access
        function (I : Big_Positive) return Element_Type)
      return Sequence
   --  Return a new sequence with New_Length elements. Each element is created
   --  by calling New_Item.

   with
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Post     => Length (Create'Result) = New_Length
       and then
          (for all I in Interval'(1, New_Length) =>
             Element_Logic_Equal (Get (Create'Result, I), New_Item (I)));

   function Transform
     (S              : Sequence;
      Transform_Item : not null access
        function (E : Element_Type) return Element_Type)
      return Sequence
   --  Return a new sequence with the same length as S. Its elements are
   --  obtained using Transform_Item on the elements of S.

   with
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Post     => Length (Transform'Result) = Length (S)
       and then
          (for all I in Interval'(1, Length (S)) =>
             Element_Logic_Equal
               (Get (Transform'Result, I), Transform_Item (Get (S, I))));

   function Count
     (S    : Sequence;
      Test : not null access function (E : Element_Type) return Boolean)
      return Big_Natural
   --  Count the number of elements on which the input Test function returns
   --  True.

   with
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Annotate => (GNATprove, Inline_For_Proof),
     Post     => Count'Result = Count (S, Length (S), Test);

   function Count
     (S    : Sequence;
      Last : Big_Natural;
      Test : not null access function (E : Element_Type) return Boolean)
      return Big_Natural
   --  Count the number of elements on which the input Test function returns
   --  True.

   with
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Pre      => Last <= Length (S),
     Post     => Count'Result <= Last;

   procedure Lemma_Count_Eq
     (S1, S2 : Sequence;
      Last   : Big_Natural;
      Test   : not null access function (E : Element_Type) return Boolean)
   --  Automatically instantiated lemma:
   --  Count returns the same value on sequences containing the same elements.

   with Ghost,
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Annotate => (GNATprove, Automatic_Instantiation),
     Pre      => Last <= Length (S1) and then Last <= Length (S2)
       and then Range_Equal (S1, S2, 1, Last),
     Post     => Count (S1, Last, Test) = Count (S2, Last, Test);

   procedure Lemma_Count_Last
     (S    : Sequence;
      Last : Big_Positive;
      Test : not null access function (E : Element_Type) return Boolean)
   --  Automatically instantiated lemma:
   --  Recursive definition of Count.

   with Ghost,
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Annotate => (GNATprove, Automatic_Instantiation),
     Pre      => Last <= Length (S),
     Post     =>
       Count (S, Last, Test) = Count (S, Last - 1, Test) +
          (if Test (Get (S, Last)) then Big_Natural'(1) else 0);

   procedure Lemma_Count_All
     (S    : Sequence;
      Last : Big_Natural;
      Test : not null access function (E : Element_Type) return Boolean)
   --  Additional lemma:
   --  Count returns Last if Test returns True on all elements of S up to Last.

   with Ghost,
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Pre      => Last <= Length (S)
       and then (for all I in Interval'(1, Last) => Test (Get (S, I))),
     Post     => Count (S, Last, Test) = Last;

   procedure Lemma_Count_None
     (S    : Sequence;
      Last : Big_Natural;
      Test : not null access function (E : Element_Type) return Boolean)
   --  Additional lemma:
   --  Count returns 0 if Test returns False on all elements of S up to Last.

   with Ghost,
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Pre      => Last <= Length (S)
       and then (for all I in Interval'(1, Last) => not Test (Get (S, I))),
     Post     => Count (S, Last, Test) = 0;

   function Filter
     (S    : Sequence;
      Test : not null access function (E : Element_Type) return Boolean)
      return Sequence
   --  Return a new sequence with all elements of S on which the input Test
   --  function returns True.

   with
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Annotate => (GNATprove, Inline_For_Proof),
     Post     => Filter'Result = Filter (S, Length (S), Test);

   function Filter
     (S    : Sequence;
      Last : Big_Natural;
      Test : not null access function (E : Element_Type) return Boolean)
      return Sequence
   --  Return a new sequence with all elements of S on which the input Test
   --  function returns True.

   with
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Pre      => Last <= Length (S),
     Post     => Length (Filter'Result) = Count (S, Last, Test)
       and then (for all E of Filter'Result => Test (E));

   procedure Lemma_Filter_Eq
     (S1, S2 : Sequence;
      Last   : Big_Natural;
      Test   : not null access function (E : Element_Type) return Boolean)
   --  Automatically instantiated lemma:
   --  Filter returns the same value on sequences containing the same elements.

   with Ghost,
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Annotate => (GNATprove, Automatic_Instantiation),
     Pre      => Last <= Length (S1) and then Last <= Length (S2)
       and then (for all I in Interval'(1, Last) =>
                   Element_Logic_Equal (Get (S1, I), Get (S2, I))),
     Post     =>
       Length (Filter (S1, Last, Test)) = Length (Filter (S2, Last, Test))
       and then
         Equal_Prefix (Filter (S1, Last, Test), Filter (S2, Last, Test));

   procedure Lemma_Filter_Last
     (S    : Sequence;
      Last : Big_Positive;
      Test : not null access function (E : Element_Type) return Boolean)
   --  Automatically instantiated lemma:
   --  Recursive definition of Filter.

   with Ghost,
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Annotate => (GNATprove, Automatic_Instantiation),
     Pre      => Last <= Length (S),
     Post     =>
       Equal_Prefix (Filter (S, Last - 1, Test), Filter (S, Last, Test)),
     Contract_Cases =>
       (Test (Get (S, Last)) =>
          Length (Filter (S, Last, Test)) =
            Length (Filter (S, Last - 1, Test)) + 1
          and then Element_Logic_Equal
            (Get (S, Last),
             Get (Filter (S, Last, Test), Length (Filter (S, Last, Test)))),
        others               =>
          Length (Filter (S, Last, Test)) =
            Length (Filter (S, Last - 1, Test)));

   procedure Lemma_Filter_All
     (S    : Sequence;
      Last : Big_Natural;
      Test : not null access function (E : Element_Type) return Boolean)
   --  Additional lemma:
   --  Filter returns the prefix of S up to Last if Test returns True on all
   --  of its elements.

   with Ghost,
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Pre      => Last <= Length (S)
       and then (for all I in Interval'(1, Last) => Test (Get (S, I))),
     Post     => Length (Filter (S, Last, Test)) = Last
       and then Equal_Prefix (Filter (S, Last, Test), S);

   function Sum
     (S     : Sequence;
      Value : not null access function (E : Element_Type) return Big_Integer)
      return Big_Integer
   --  Sum the result of the Value function on all elements of S

   with
     Global   => null,
     Annotate => (GNATprove, Inline_For_Proof),
     Annotate => (GNATprove, Higher_Order_Specialization),
     Post     => Sum'Result = Sum (S, Length (S), Value);

   function Sum
     (S     : Sequence;
      Last  : Big_Natural;
      Value : not null access function (E : Element_Type) return Big_Integer)
      return Big_Integer
   --  Sum the result of the Value function on all elements of S up to Last

   with
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Pre      => Last <= Length (S),
     Post     => (if Last = 0 then Sum'Result = 0);

   procedure Lemma_Sum_Eq
     (S1, S2 : Sequence;
      Last   : Big_Natural;
      Value  : not null access function (E : Element_Type) return Big_Integer)
   --  Automatically instantiated lemma:
   --  Sum returns the same value on sequences containing the same elements.

   with Ghost,
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Annotate => (GNATprove, Automatic_Instantiation),
     Pre      => Last <= Length (S1) and then Last <= Length (S2)
       and then Range_Equal (S1, S2, 1, Last),
     Post     => Sum (S1, Last, Value) = Sum (S2, Last, Value);

   procedure Lemma_Sum_Last
     (S     : Sequence;
      Last  : Big_Positive;
      Value : not null access function (E : Element_Type) return Big_Integer)
   --  Automatically instantiated lemma:
   --  Recursive definition of Sum.

   with Ghost,
     Global   => null,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Annotate => (GNATprove, Automatic_Instantiation),
     Pre      => Last <= Length (S),
     Post     => Sum (S, Last, Value) =
       Sum (S, Last - 1, Value) + Value (Get (S, Last));

end SPARK.Containers.Functional.Infinite_Sequences.Higher_Order;
