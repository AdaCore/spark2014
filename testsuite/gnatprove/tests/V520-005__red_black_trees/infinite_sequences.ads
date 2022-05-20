with Ada.Containers.Functional_Maps;
with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;
with Big_Intervals; use Big_Intervals;

package Infinite_Sequences with SPARK_Mode is
   type Sequence is private;
   function First (S : Sequence) return Big_Positive;
   function Last (S : Sequence) return Big_Natural with
     Post => Last'Result >= First (S) - 1;
   function Get (S : Sequence; I : Big_Positive) return Integer with
     Pre => In_Range (I, First (S), Last (S));
   function Empty (Fst : Big_Positive) return Sequence with
     Post => First (Empty'Result) = Fst and Last (Empty'Result) = Fst - 1;

   function "=" (X, Y : Sequence) return Boolean with
     Post => "="'Result =
       (First (X) = First (Y) and then Last (X) = Last (Y)
        and then
          (for all I in Interval'(First (X), Last (X)) =>
             Get (X, I) = Get (Y, I)));

   function "<=" (X, Y : Sequence) return Boolean with
     Post => "<="'Result =
       (First (Y) <= First (X) and then Last (X) <= Last (Y)
        and then
          (for all I in Interval'(First (X), Last (X)) =>
             Get (X, I) = Get (Y, I)));

   function Is_Concat (S1 : Sequence; I2 : Integer; S3 : Sequence; R : Sequence) return Boolean is
     (First (R) = First (S1) and then Last (R) = Last (S3)
      and then First (S3) = Last (S1) + 2
      and then S1 <= R
      and then Get (R, Last (S1) + 1) = I2
      and then S3 <= R)
     with Ghost;
   --  Returns true if R is S1 & I2 & S3. No sliding are allowed, S3 should
   --  start at the end of S1 plus 1.

   function Concat (S1 : Sequence; I2 : Integer; S3 : Sequence) return Sequence with
     Pre  => First (S3) = Last (S1) + 2,
     Post => Is_Concat (S1, I2, S3, Concat'Result);
private
   package Maps is new Ada.Containers.Functional_Maps
     (Big_Positive, Integer);

   function Is_Valid
     (Fst : Big_Positive;
      Lst : Big_Natural;
      M   : Maps.Map) return Boolean;

   type Sequence is record
      Content : Maps.Map;
      First   : Big_Positive := 1;
      Last    : Big_Natural := 0;
   end record with
     Predicate => Is_Valid (First, Last, Content);
end Infinite_Sequences;
