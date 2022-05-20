--  This example is a SPARK version of the running example used by Astrauskas
--  et all in their article defining pledges. We respect to the Rust version,
--  we had to introduce a few modifications:
--   * We had to use access for most parameters instead of top level objects.
--     It is needed for Nth_Point which is a traversal function and it felt
--     more consistent to do the same for other functions.
--   * We had to store Points inside a pointer in Route so that we can return
--     an access to it in Nth_Point.
--   * We cannot copy values of a deep type, so 'Old is not availlable on
--     routes. We introduced a Sequence to store all the elements in the list
--     so that we could speak about values preserved by Nth_Point and
--     Shift_Nth_X.

with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;
with Ada.Containers.Functional_Vectors; -- use infinite sequences
with Big_Intervals; use Big_Intervals;
package Test_Route with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   type Point is record
      X, Y : Integer;
   end record;
   type Point_Acc is not null access Point;
   --  A point is a pair of coordinates

   procedure Shift_X (P : not null access Point; S : Integer) with
     Pre  => (if S > 0 then P.X <= Integer'Last - S
              else P.X >= Integer'First - S),
     Post => P.X = P.X'Old + S and P.Y = P.Y'Old;
   --  Shift the X coordinate of P by S

   type Route;
   type Route_Acc is access Route;
   type Route is record
      Current : Point_Acc;
      Rest    : Route_Acc;
   end record;
   --  A route is a list of points

   function Length (R : access constant Route) return Big_Natural is
     (if R = null then 0
      else Length (R.Rest) + 1)
   with Subprogram_Variant => (Structural => R);
   --  Number of points in the route

   function Nth_X (R : access constant Route; N : Big_Positive) return Integer is
     (if N = 1 then R.Current.X else Nth_X (R.Rest, N - 1))
   with Subprogram_Variant => (Structural => R),
     Pre => N <= Length (R);
   --  Value of the X coordinate of the point at position N in Route

   package Int_Seqs is new Ada.Containers.Functional_Vectors
     (Index_Type   => Positive,
      Element_Type => Integer);
   type Int_Seq is new Int_Seqs.Sequence;
   --  Sequence of Integers to be used to model the X coordinates of elements
   --  of a route.

   function All_X (R : access constant Route) return Int_Seq with
     Pre  => Length (R) <= To_Big_Integer (Integer'Last),
     Post => To_Big_Integer (Last (All_X'Result)) = Length (R)
     and (for all N in 1 .. Last (All_X'Result) =>
              Get (All_X'Result, N) = Nth_X (R, To_Big_Integer (N)));
   --  Gets all the X coordinates of points of a route

   function At_End
     (P : access constant Route) return access constant Route
   is
     (P)
   with Ghost,
     Annotate => (GNATprove, At_End_Borrow);
   --  Pledge function, used to mark assertions as pledges for the analysis tool

   function At_End
     (P : access constant Point) return access constant Point
   is
     (P)
   with Ghost,
     Annotate => (GNATprove, At_End_Borrow);
   --  Pledge function, used to mark assertions as pledges for the analysis tool

   function Nth_Point (R : access Route; N : Big_Positive) return not null access Point
   --  Borrows the point at position N in Route
   with
     Pre  => N <= Length (R),

     --  The points of R are preserved but for the one at position N which is
     --  replaced by the new value of Nth_Point'Result. Just like the one for
     --  Rust, the contract here only cares about the X coordinate. Adding the
     --  Y coordinate wouldn't be more complicated.

     Post => Length (At_End (R)) = Length (R)
        and Nth_X (At_End (R), N) = At_End (Nth_Point'Result).X
        and (for all I in Interval'(1, Length (R)) =>
               (if I /= N then Nth_X (At_End (R), I) = Nth_X (R, I)));

   procedure Shift_Nth_X (R : access Route; N : Big_Positive; S : Integer) with
   --  Shift the X coordinate of the point at position N by S

     Pre  => N <= Length (R)
     and then Length (R) <= To_Big_Integer (Integer'Last) --  Remove with infinite sequences
     and then (if S > 0 then Nth_X (R, N) <= Integer'Last - S
               else Nth_X (R, N) >= Integer'First - S),

     --  The points of R are preserved but for the one at position N whose X
     --  coordinate is shifted by S. Just like the one for
     --  Rust, the contract here only cares about the X coordinate. Adding the
     --  Y coordinate wouldn't be more complicated.

     Post => Length (R) = Length (R)'Old
     and then Nth_X (R, N) = Nth_X (R, N)'Old + S
     and then (for all I in Interval'(1, Length (R)) =>
                 (if I /= N then Nth_X (R, I) = Get (All_X (R)'Old, To_Integer (I))));

end Test_Route;
