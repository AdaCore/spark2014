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

   function Pledge (L : access constant List_Cell; P : Boolean) return Boolean is
     (P)
   with Ghost,
     Annotate => (GNATProve, Pledge);

   function Pledge (L : access constant Integer; P : Boolean) return Boolean is
     (P)
   with Ghost,
     Annotate => (GNATProve, Pledge);

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
           -- pragma Assert (Nth (L, I) = V);
            return I;
         end if;
         X := X.Next;
         I := I + 1;
      end loop;
      return 0;
   end Linear_Search;

   package Int_Seqs is new Ada.Containers.Functional_Vectors
     (Index_Type   => Positive,
      Element_Type => Integer);
   type Int_Seq is new Int_Seqs.Sequence;

   function All_Data (R : access constant List_Cell) return Int_Seq with
     Post => Last (All_Data'Result) = Length (R)
     and (for all N in 1 .. Length (R) =>
              Get (All_Data'Result, N) = Nth (R, N))
   is
   begin
      return A : Int_Seq do
         for N in 1 .. Length (R) loop
            pragma Loop_Invariant (Last (A) = N - 1);
            pragma Loop_Invariant
              (for all I in 1 .. N - 1 => Get (A, I) = Nth (R, I));
            A := Add (A, Nth (R, N));
         end loop;
      end return;
   end All_Data;

   function Linear_Search (L : access List_Cell; V : Integer) return access Integer with
     Pre => Length (L) < Integer'Last,
     Contract_Cases =>
       ((for all I in 1 .. Length (L) => Nth (L, I) /= V) =>
          Linear_Search'Result = null
          and then Pledge (Linear_Search'Result, (for all K in 1 .. Length (L) => Nth (L, K) = Get (All_Data (L)'Old, K))),
        others                                            =>
          Linear_Search'Result /= null
          and then Linear_Search'Result.all = V
          and then Pledge (Linear_Search'Result,
          (for all K in 1 .. Length (L) =>
             (if Get (All_Data (L)'Old, K) /= V then Nth (L, K) = Get (All_Data (L)'Old, K))))
          and then Pledge (Linear_Search'Result,
          (for some K in 1 .. Length (L) =>
             Get (All_Data (L)'Old, K) = V and then Nth (L, K) = Linear_Search'Result.all)))
   is
      I : Natural := 0 with Ghost;
      O : constant Int_Seq := All_Data (L) with Ghost;
      X : access List_Cell := L;
   begin
      while X /= null loop
         pragma Loop_Invariant (I = Length (X)'Loop_Entry - Length (X));
         pragma Loop_Invariant
           (for all K in I + 1 .. Length (L) => Nth (X, K - I) = Nth (L, K));
         pragma Loop_Invariant (for all K in 1 .. I => Nth (L, K) /= V);
         pragma Loop_Invariant
           (Pledge (X, Length (L) = Integer'Min (Integer'Last - I, Length (X)) + I));
         pragma Loop_Invariant
           (Pledge (X, (for all K in 1 .. I => Nth (L, K) = Get (O, K))));
         pragma Loop_Invariant
           (Pledge (X, (for all K in I + 1 .. Length (L) => Nth (L, K) = Nth (X, K - I))));

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
