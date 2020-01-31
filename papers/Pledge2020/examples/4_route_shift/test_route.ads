--  This example is a SPARK version of the running example used by Astrauskas
--  et all in their article defining pledges. We respect to the Rust version,
--  we had to introduce a few modifications:
--   * We had to handle possible overflows, both in length and shift.
--     For Shift, we have added a precondition, while for Length, we went for
--     a saturating addition to make contracts more readable.
--   * The pure functions are annotating as terminating in SPARK. As they are
--     recursive and SPARK cannot handle (yet) proof of recursive functions, we
--     had to justify them.
--   * We had to use access for most parameters instead of top level objects.
--     It is needed for Nth_Point which is a traversal function and it felt
--     more consistent to do the same for other functions.
--   * We had to store Points inside a pointer in Route so that we can return
--     an access to it in Nth_Point.
--   * We cannot copy values of a deep type, so 'Old is not availlable on
--     routes. We introduced a Sequence to store all the elements in the list
--     so that we could speak about values preserved by Nth_Point and
--     Shift_Nth_X.

with Ada.Containers.Functional_Vectors;
package Test_Route with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   type My_Nat is new Natural;
   subtype My_Pos is My_Nat range 1 .. My_Nat'Last;

   function "+" (X, Y : My_Nat) return My_Nat is
     (if My_Nat'Last - X < Y then My_Nat'Last
      else My_Nat (Integer (X) + Integer (Y)));
   --  Saturating addition to simplify contracts

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

   function Length (R : access constant Route) return My_Nat is
     (if R = null then 0
      else Length (R.Rest) + 1)
   with Annotate => (GNATprove, Terminating);
   --  Number of points in the route. It saturates at My_Nat'Last

   pragma Annotate
     (GNATprove, False_Positive, """Length"" might not terminate",
      "Recursive calls only occur on structuraly smaller values");

   function Nth_X (R : access constant Route; N : My_Pos) return Integer is
     (if N = 1 then R.Current.X else Nth_X (R.Rest, N - 1))
   with Annotate => (GNATprove, Terminating),
     Pre => N <= Length (R);
   --  Value of the X coordinate of the point at position N in Route

   pragma Annotate
     (GNATprove, False_Positive, """Nth_X"" might not terminate",
      "Recursive calls only occur on structuraly smaller values");

   package Int_Seqs is new Ada.Containers.Functional_Vectors
     (Index_Type   => My_Pos,
      Element_Type => Integer);
   type Int_Seq is new Int_Seqs.Sequence;
   --  Sequence of Integers to be used to model the X coordinates of elements
   --  of a route.

   function All_X (R : access constant Route) return Int_Seq with
     Post => Last (All_X'Result) = Length (R)
     and (for all N in 1 .. Length (R) =>
              Get (All_X'Result, N) = Nth_X (R, N));
   --  Gets all the X coordinates of points of a route

   function Pledge
     (Dummy    : access constant Point;
      Property : Boolean) return Boolean
   is
     (Property)
   with Ghost,
     Annotate => (GNATProve, Pledge);
   --  Pledge function, used to mark assertions as pledges for the analysis tool

   function Nth_Point (R : access Route; N : My_Pos) return not null access Point
   --  Borrows the point at position N in Route
   with
     Pre  => N < Length (R),

     --  The points of R are preserved but for the one at position N which is
     --  replaced by the new value of Nth_Point'Result. Just like the one for
     --  Rust, the contract here only cares about the X coordinate. Adding the
     --  Y coordinate wouldn't be more complicated.

     Post => Pledge
       (Nth_Point'Result,
        Length (R) = Length (R)'Old
        and Nth_X (R, N) = Nth_Point'Result.X
        and (for all I in 1 .. Length (R) =>
               (if I /= N then Nth_X (R, I) = Get (All_X (R)'Old, I))));

   procedure Shift_Nth_X (R : access Route; N : My_Pos; S : Integer) with
   --  Shift the X coordinate of the point at position N by S

     Pre  => N < Length (R)
     and then (if S > 0 then Nth_X (R, N) <= Integer'Last - S
               else Nth_X (R, N) >= Integer'First - S),

     --  The points of R are preserved but for the one at position N whose X
     --  coordinate is shifted by S. Just like the one for
     --  Rust, the contract here only cares about the X coordinate. Adding the
     --  Y coordinate wouldn't be more complicated.

     Post => Length (R) = Length (R)'Old
     and then Nth_X (R, N) = Nth_X (R, N)'Old + S
     and then (for all I in 1 .. Length (R) =>
              (if I /= N then Nth_X (R, I) = Get (All_X (R)'Old, I)));

end Test_Route;
