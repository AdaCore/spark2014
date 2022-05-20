with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;
with Big_Intervals; use Big_Intervals;

package Linear_Search with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);
   type Int_Acc is access Integer;
   type List_Cell;
   type List is access List_Cell;
   type List_Cell is record
      Data : not null Int_Acc;
      Next : List;
   end record;
   --  List of integers. Integers are stored inside pointers to be able to
   --  borrow a single cell of a list.

  function Length (L : access constant List_Cell) return Big_Natural is
   (if L = null then 0 else Length (L.Next) + 1)
  with Ghost,
     Subprogram_Variant => (Structural => L);
   --  Number of elements in the list

  function Nth (L : access constant List_Cell; N : Big_Positive) return Integer is
   (if N = 1 then L.Data.all else Nth (L.Next, N - 1))
  with  Ghost,
    Subprogram_Variant => (Structural => L),
    Pre => N <= Length (L);
   --  Element at position N in the list

   function At_End
     (L : access constant List_Cell) return access constant List_Cell
   is
     (L)
   with Ghost,
     Annotate => (GNATprove, At_End_Borrow);
   --  Pledge function, used to mark assertions as pledges for the analysis tool

   function At_End
     (I : access constant Integer) return access constant Integer
   is
     (I)
   with Ghost,
     Annotate => (GNATprove, At_End_Borrow);
   --  Pledge function, used to mark assertions as pledges for the analysis tool

   function Linear_Search (L : access constant List_Cell; V : Integer) return Big_Natural with
   --  Search an element in a list, return its position

     Contract_Cases =>

       --  If V is not in L, return 0

       ((for all I in Interval'(1, Length (L)) => Nth (L, I) /= V) =>
          Linear_Search'Result = 0,

       --  Otherwise, return the position of the first occurrence of V in L

        others                                            =>
          In_Range (Linear_Search'Result, 1, Length (L))
          and then Nth (L, Linear_Search'Result) = V
          and then
          (for all K in Interval'(1, Linear_Search'Result - 1) => Nth (L, K) /= V));

   function Linear_Search (L : access List_Cell; V : Integer) return access Integer with
   --  Search an element in a list, borrows the corresponding value

     Contract_Cases =>

       --  If V is not in L, return null

       ((for all I in Interval'(1, Length (L)) => Nth (L, I) /= V) =>
          Linear_Search'Result = null

       --  L is frozen

        and then
          (for all K in Interval'(1, Length (At_End (L))) => Nth (At_End (L), K) = Nth (L, K)),

       --  Otherwise, return a valid pointer designating V

        others                                            =>
          Linear_Search'Result /= null
          and then Linear_Search'Result.all = V

       --  The first occurrence of V in L is designated by Linear_Search'Result

          and then
            Nth (At_End (L), Linear_Search (L, V)) = At_End (Linear_Search'Result).all

       --  Other elements are frozen

          and then
          (for all K in Interval'(1, Length (L)) =>
             (if K /= Linear_Search (L, V) then Nth (At_End (L), K) = Nth (L, K))));

end Linear_Search;
