with Ada.Containers.Functional_Vectors;
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

  function Length (L : access constant List_Cell) return Natural is
   (if L = null then 0
    else Natural'Min (Natural'Last - 1, Length (L.Next)) + 1)
  with Ghost,
     Annotate => (GNATprove, Terminating);
   --  Number of elements in the list, it saturates at Natural'length.

   pragma Annotate
     (GNATprove, False_Positive, """Length"" might not terminate",
      "Recursive calls only occur on structuraly smaller values");

  function Nth (L : access constant List_Cell; N : Positive) return Integer is
   (if N = 1 then L.Data.all else Nth (L.Next, N - 1))
  with  Ghost,
    Annotate => (GNATprove, Terminating),
    Pre => N <= Length (L);
   --  Element at position N in the list

   pragma Annotate
     (GNATprove, False_Positive, """Nth"" might not terminate",
      "Recursive calls only occur on structuraly smaller values");

   function Pledge
     (Dummy    : access constant List_Cell;
      Property : Boolean) return Boolean
   is
     (Property)
   with Ghost,
     Annotate => (GNATProve, Pledge);
   --  Pledge function, used to mark assertions as pledges for the analysis tool

   function Pledge
     (Dummy    : access constant Integer;
      Property : Boolean) return Boolean
   is
     (Property)
   with Ghost,
     Annotate => (GNATProve, Pledge);
   --  Pledge function, used to mark assertions as pledges for the analysis tool

   package Int_Seqs is new Ada.Containers.Functional_Vectors
     (Index_Type   => Positive,
      Element_Type => Integer);
   type Int_Seq is new Int_Seqs.Sequence;
   --  Sequence of integers, used to represent the list in a copyable way

   function All_Data (R : access constant List_Cell) return Int_Seq with
     Ghost,
     Post => Last (All_Data'Result) = Length (R)
     and (for all N in 1 .. Length (R) =>
              Get (All_Data'Result, N) = Nth (R, N));
   --  First Length (R) values of R

   function Linear_Search (L : access constant List_Cell; V : Integer) return Natural with
   --  Search an element in a list, return its position

     Pre => Length (L) < Integer'Last,
     Contract_Cases =>

       --  If V is not in L, return 0

       ((for all I in 1 .. Length (L) => Nth (L, I) /= V) =>
          Linear_Search'Result = 0,

       --  Otherwise, return the position of the first occurrence of V in L

        others                                            =>
          Linear_Search'Result in 1 .. Length (L)
          and then Nth (L, Linear_Search'Result) = V
          and then
          (for all K in 1 .. Linear_Search'Result - 1 => Nth (L, K) /= V));

   function Linear_Search (L : access List_Cell; V : Integer) return access Integer with
   --  Search an element in a list, borrows the corresponding value

     Pre => Length (L) < Integer'Last,
     Contract_Cases =>

       --  If V is not in L, return null

       ((for all I in 1 .. Length (L) => Nth (L, I) /= V) =>
          Linear_Search'Result = null

       --  L is frozen

        and then
          Pledge (Linear_Search'Result,
          (for all K in 1 .. Length (L) => Nth (L, K) = Get (All_Data (L)'Old, K))),

       --  Otherwise, return a valid pointer designating V

        others                                            =>
          Linear_Search'Result /= null
          and then Linear_Search'Result.all = V

       --  The first occurrence of V in L is designated by Linear_Search'Result

          and then
          Pledge (Linear_Search'Result,
            Nth (L, Natural'(Linear_Search (L, V))'Old) = Linear_Search'Result.all)

       --  Other elements are frozen

          and then
          Pledge (Linear_Search'Result,
          (for all K in 1 .. Length (L) =>
             (if K /= Natural'(Linear_Search (L, V))'Old then Nth (L, K) = Get (All_Data (L)'Old, K)))));

end Linear_Search;
