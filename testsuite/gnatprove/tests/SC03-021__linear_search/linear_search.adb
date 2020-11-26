with Ada.Containers.Functional_Vectors;
procedure Linear_Search with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);
   type Int_Acc is access Integer;
   type List_Cell;
   type List is access List_Cell;
   type List_Cell is record
      Data : not null Int_Acc;
      Next : List;
   end record;

  function Length (L : access constant List_Cell) return Natural is
   (if L = null then 0
    else Natural'Min (Natural'Last - 1, Length (L.Next)) + 1)
  with Annotate => (GNATprove, Terminating);

  function Nth (L : access constant List_Cell; N : Positive) return Integer is
   (if N = 1 then L.Data.all else Nth (L.Next, N - 1))
  with Annotate => (GNATprove, Terminating),
    Pre => N <= Length (L);

   function At_End_Borrow (L : access constant List_Cell) return access constant List_Cell is
     (L)
   with Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   function At_End_Borrow (I : access constant Integer) return access constant Integer is
     (I)
   with Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   function Linear_Search (L : access constant List_Cell; V : Integer) return Natural with
     Pre => Length (L) < Integer'Last,
     Contract_Cases =>
       ((for all I in 1 .. Length (L) => Nth (L, I) /= V) =>
          Linear_Search'Result = 0,
        others                                            =>
          Linear_Search'Result in 1 .. Length (L)
          and then Nth (L, Linear_Search'Result) = V)
   is
      X : access constant List_Cell := L;
      I : Positive := 1;
   begin
      while X /= null loop
         pragma Loop_Invariant (I = Length (X)'Loop_Entry - Length (X) + 1);
         pragma Loop_Invariant (for all K in 1 .. I - 1 => Nth (L, K) /= V);
         pragma Loop_Invariant
           (for all K in 1 .. Length (X) => Nth (X, K) = Nth (L, K + I - 1));
         pragma Loop_Invariant
           (for all K in I .. Length (L) => Nth (L, K) = Nth (X, K - I + 1));
         if X.Data.all = V then
            pragma Assert (Nth (L, I) = V);
            return I;
         end if;
         X := X.Next;
         I := I + 1;
      end loop;
      return 0;
   end Linear_Search;

   function Linear_Search (L : access List_Cell; V : Integer) return access Integer with
     Pre => Length (L) < Integer'Last,
     Contract_Cases =>
       ((for all I in 1 .. Length (L) => Nth (L, I) /= V) =>
          Linear_Search'Result = null
          and then (for all K in 1 .. Length (At_End_Borrow (L)) => Nth (At_End_Borrow (L), K) = Nth (L, K)),
        others                                            =>
          Linear_Search'Result /= null
          and then Linear_Search'Result.all = V
          and then
          (for all K in 1 .. Length (At_End_Borrow (L)) =>
             (if Nth (L, K) /= V then Nth (At_End_Borrow (L), K) = Nth (L, K)))
          and then
          (for some K in 1 .. Length (L) =>
             Nth (L, K) = V
             and then Nth (At_End_Borrow (L), K) = At_End_Borrow (Linear_Search'Result).all))
   is
      I : Natural := 0 with Ghost;
      X : access List_Cell := L;
   begin
      while X /= null loop
         pragma Loop_Invariant (I = Length (X)'Loop_Entry - Length (X));
         pragma Loop_Invariant
           (for all K in I + 1 .. Length (L) => Nth (X, K - I) = Nth (L, K));
         pragma Loop_Invariant (for all K in 1 .. I => Nth (L, K) /= V);
         pragma Loop_Invariant
           (Length (At_End_Borrow (L)) = Integer'Min (Integer'Last - I, Length (At_End_Borrow (X))) + I);
         pragma Loop_Invariant
           (for all K in 1 .. I => Nth (At_End_Borrow (L), K) = Nth (L, K));
         pragma Loop_Invariant
           (for all K in I + 1 .. Length (At_End_Borrow (L)) =>
              Nth (At_End_Borrow (L), K) = Nth (At_End_Borrow (X), K - I));

         if X.Data.all = V then
            pragma Assert (Nth (L, I + 1) = V);
            return X.Data;
         end if;

         X := X.Next;
         I := I + 1;
      end loop;
      return null;
   end Linear_Search;

begin
   null;
end Linear_Search;
