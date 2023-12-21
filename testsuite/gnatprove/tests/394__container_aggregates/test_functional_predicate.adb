with Test_Functional_Predicate_Instances; use Test_Functional_Predicate_Instances;
with SPARK.Big_Integers; use SPARK.Big_Integers;

procedure Test_Functional_Predicate with SPARK_Mode is

   One : Integer := 1;

   procedure Test_Vectors with
     Global => One;

   procedure Test_Vectors is
      use Vectors;
      X : Sequence := [R(1), R(2), R(One), R(4), R(5)];  -- @PREDICATE_CHECK:FAIL
   begin
      null;
   end Test_Vectors;

   procedure Test_Sets with
     Global => One;

   procedure Test_Sets is
      use Sets;
      X : Set := [R(One), R(2), R(3), R(4), R(5)];  -- @PREDICATE_CHECK:FAIL
   begin
      null;
   end Test_Sets;

   procedure Test_Maps with
     Global => One;

   procedure Test_Maps is
      use Maps;
      X : Map := [1 => R(One), 2 => R(2), 3 => R(3), 4 => R(4), 5 => R(5)];  -- @PREDICATE_CHECK:FAIL
   begin
      null;
   end Test_Maps;

   procedure Test_Seqs with
     Global => One;

   procedure Test_Seqs is
      use Seqs;
      X : Sequence := [R(1), R(2), R(3), R(One), R(5)];  -- @PREDICATE_CHECK:FAIL
   begin
      null;
   end Test_Seqs;

   procedure Test_Multisets (Val : Big_Integer) with
     Global => null;

   procedure Test_Multisets (Val : Big_Integer) is
      use Multisets;
      X : Multiset := [1 => Val, 2 => 2, 3 => 3, 4 => 4, 5 => 5];  -- @PREDICATE_CHECK:FAIL
   begin
      null;
   end Test_Multisets;

begin
   null;
end Test_Functional_Predicate;
