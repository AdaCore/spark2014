with SPARK.Big_Integers; use SPARK.Big_Integers;
with SPARK.Containers.Functional.Infinite_Sequences;

procedure Test_Eq_Infinite_Sequences with SPARK_Mode is

   --  Instance with a private type whose equality is the logical equality.
   --  Everything should be proved.

   package Nested_1 is
      type P is private;
   private
      pragma SPARK_Mode (Off);
      type P is new Integer;
   end Nested_1;
   use Nested_1;

   package Seq_1 is new
     SPARK.Containers.Functional.Infinite_Sequences
       (Nested_1.P,
        Use_Logical_Equality => True);
   use type Seq_1.Sequence;

   --  Test that extentionality axiom works as expected. The second test does
   --  not mention "=" so the axiom is not available and it is expected that it
   --  cannot be proved.

   function F (X : Seq_1.Sequence) return Integer
   with Import, Global => null;

   procedure Test_Eq (X, Y : Seq_1.Sequence)
   with Pre => X = Y, Post => F (X) = F (Y);

   procedure Test_Eq (X, Y : Seq_1.Sequence) is null;

   procedure Test_Eq_2 (X, Y : Seq_1.Sequence)
   with
     Pre  =>
       Seq_1.Length (X) = Seq_1.Length (Y)
       and then (for all I in X => Seq_1.Get (X, I) = Seq_1.Get (Y, I)),
     Post => F (X) = F (Y);  --  Unprovable for now

   procedure Test_Eq_2 (X, Y : Seq_1.Sequence) is null;

   procedure Test_Eq_3 (X, Y : Seq_1.Sequence)
   with
     Pre  =>
       Seq_1.Length (X) = Seq_1.Length (Y)
       and then (for all I in X => Seq_1.Get (X, I) = Seq_1.Get (Y, I)),
     Post => F (X) = F (Y);

   procedure Test_Eq_3 (X, Y : Seq_1.Sequence) is
   begin
      pragma Assert (X = Y);
   end Test_Eq_3;

   --  Instance with a private type whose equality is not the logical equality.
   --  There should be a single failed check on the proof of the lemma.

   package Nested_2 is
      type P is private;
   private
      pragma SPARK_Mode (Off);
      type P is new Float;
   end Nested_2;
   use Nested_2;

   package Seq_2 is new
     SPARK.Containers.Functional.Infinite_Sequences
       (Nested_2.P,
        Use_Logical_Equality => True);

   --  Instance with a private type whose equality is not the logical equality,
   --  but with a Lemma.
   --  Everything should be proved.

   function Logical_Eq (X, Y : Nested_2.P) return Boolean
   with Ghost, Import, Global => null, Annotate => (GNATprove, Logical_Equal);

   procedure Lemma_Eq_Is_Logical (X, Y : Nested_2.P)
   with
     Ghost,
     Import,
     Global => null,
     Always_Terminates,
     Post   => (X = Y) = Logical_Eq (X, Y);

   package Seq_3 is new
     SPARK.Containers.Functional.Infinite_Sequences
       (Nested_2.P,
        Use_Logical_Equality => True,
        Eq_Logical_Eq        => Lemma_Eq_Is_Logical);

begin
   null;
end;
