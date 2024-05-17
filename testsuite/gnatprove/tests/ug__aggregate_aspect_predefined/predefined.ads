with SPARK.Big_Integers;  use SPARK.Big_Integers;
with SPARK.Big_Intervals; use SPARK.Big_Intervals;

package Predefined with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);
   type List is private with
     Aggregate => (Empty => Empty_List, Add_Unnamed => Add),
     Annotate  => (GNATprove, Container_Aggregates, "Predefined_Sequences");

   function Empty_List return List;

   function First return Big_Positive is (1) with
     Annotate => (GNATprove, Container_Aggregates, "First");

   function Length (L : List) return Big_Natural with
     Subprogram_Variant => (Structural => L),
     Annotate => (GNATprove, Container_Aggregates, "Last");

   function Get (L : List; P : Big_Positive) return Integer with
     Pre => P <= Length (L),
     Subprogram_Variant => (Structural => L),
     Annotate => (GNATprove, Container_Aggregates, "Get");

   function Eq (L1, L2 : List) return Boolean is
     (Length (L1) = Length (L2)
      and then
        (for all I in Interval'(1, Length (L1)) =>
              Get (L1, I) = Get (L2, I)));

   function Copy (L : List) return List with
     Subprogram_Variant => (Structural => L),
     Post => Eq (L, Copy'Result);

   procedure Add (L : in out List; E : Integer) with
     Always_Terminates,
     Post => Length (L) = Length (L)'Old + 1
     and then Get (L, Length (L)) = E
     and then (for all I in Interval'(1, Length (L) - 1) =>
                 Get (L, I) = Get (Copy (L)'Old, I));

private
   type List_Cell;
   type List is access List_Cell;
   type List_Cell is record
      Data : Integer;
      Next : List;
   end record;

   function Length (L : List) return Big_Natural is
     (if L = null then 0 else 1 + Length (L.Next));

   function Get (L : List; P : Big_Positive) return Integer is
     (if P = Length (L) then L.Data else Get (L.Next, P));

   function Empty_List return List is (null);
end Predefined;
