with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;

package Big_Intervals with SPARK_Mode is
   --  Intervals of big integers to allow iteration. To be replaced by the
   --  appropriate library unit when there is one.

   type Interval is record
      First, Last : Big_Integer;
   end record
     with Iterable =>
       (First       => First,
        Next        => Next,
        Has_Element => In_Range);

   function First (I : Interval) return Big_Integer is
     (I.First);

   function Next (Dummy : Interval; X : Big_Integer) return Big_Integer is
     (X + 1);

   function In_Range (I : Interval; X : Big_Integer) return Boolean is
     (In_Range (X, I.First, I.Last));
end Big_Intervals;
