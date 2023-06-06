with SPARK.Containers.Functional.Infinite_Sequences;
with SPARK.Big_Integers; use SPARK.Big_Integers;

package Int_Lists with SPARK_Mode, Always_Terminates is

   package Seqs is new SPARK.Containers.Functional.Infinite_Sequences (Integer);
   use Seqs;

   type List is private;
   type List_Acc is access List;

   function Model (L : access constant List) return Sequence with
     Post => (Length (Model'Result) = 0) = (L = null) ;

   function Lemma_Model_Def (L : access constant List) return Boolean with
     Ghost,
     Global => null,
     Post => Lemma_Model_Def'Result
     and then (if L = null then Length (Model (L)) = 0 else Model (L) = Add (Model (Peek (L)), Get (L)));

   function At_End (L : access constant List) return access constant List is (L) with
     Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   function Get (L : not null access constant List) return Integer with
     Global => null,
     Post => Get'Result = Get (Model (L), Length (Model (L))'Old);

   procedure Set (L : not null access List; D : Integer) with
     Post => Model (L) = Set (Model (L)'Old, Length (Model (L))'Old, D);

   procedure Insert (L : in out List_Acc; D : Integer) with
     Post => Model (L) = Add (Model (L)'Old, D);

   procedure Delete (L : in out List_Acc) with
     Pre => L /= null,
     Post => Model (L) = Remove (Model (L)'Old, Length (Model (L))'Old);

   function Next (L : not null access List) return access List with
     Post => Model (At_End (L)) = Add (Model (At_End (Next'Result)), Get(L));

   function Peek (L : not null access constant List) return access constant List;

private

   type List is record
      D : Integer;
      N : List_Acc;
   end record;

   function Get (L : not null access constant List) return Integer is (L.D);

   function Peek (L : not null access constant List) return access constant List is (L.N);

end Int_Lists;
