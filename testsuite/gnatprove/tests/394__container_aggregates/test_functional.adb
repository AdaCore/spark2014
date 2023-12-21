with Test_Functional_Instances; use Test_Functional_Instances;
with SPARK.Big_Integers; use SPARK.Big_Integers;

procedure Test_Functional with SPARK_Mode is

   One : Integer := 1;

   procedure Test_Vectors with
     Global => One;

   procedure Test_Vectors is
      use Vectors;
      X : Sequence := [1, 2, One, 4, 5];  -- @RANGE_CHECK:FAIL
   begin
      null;
   end Test_Vectors;

   procedure Test_Sets with
     Global => One;

   procedure Test_Sets is
      use Sets;
      X : Set := [One, 2, 3, 4, 5];  -- @RANGE_CHECK:FAIL
   begin
      null;
   end Test_Sets;

   procedure Test_Maps with
     Global => One;

   procedure Test_Maps is
      use Maps;
      X : Map := [1 => One, 2 => 2, 3 => 3, 4 => 4, 5 => 5];  -- @RANGE_CHECK:FAIL
   begin
      null;
   end Test_Maps;

   procedure Test_Seqs with
     Global => One;

   procedure Test_Seqs is
      use Seqs;
      X : Sequence := [1, 2, 3, One, 5];  -- @RANGE_CHECK:FAIL
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
end Test_Functional;
