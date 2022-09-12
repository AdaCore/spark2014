with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;
with SPARK.Big_Intervals; use SPARK.Big_Intervals;

package Test_List with SPARK_Mode is

   type List_Cell;
   type List is access List_Cell;
   type List_Cell is record
      Data : Integer;
      Next : List;
   end record;

   function Length (L : access constant List_Cell) return Big_Natural is
     (if L = null then 0 else Length (L.Next) + 1)
   with Ghost,
        Subprogram_Variant => (Structural => L);
   --  Number of elements in the list. Returns My_Nat'Last if there is more
   --  than My_Nat'Last elements in the list.

   function Nth (L : access constant List_Cell; N : Big_Positive) return Integer is
     (if N = 1 then L.Data else Nth (L.Next, N - 1))
   with Ghost,
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

   procedure Set_All_To_Zero (X : List) with
     Post => Length (X) = Length (X)'Old
     and (for all I in Interval'(1, Length (X)) => Nth (X, I) = 0);
   --  Set all elements of a list to 0

end Test_List;
