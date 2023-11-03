with SPARK.Big_Integers; use SPARK.Big_Integers;
with SPARK.Containers.Functional.Sets;
with SPARK.Containers.Functional.Maps;
with SPARK.Containers.Functional.Multisets;
with SPARK.Containers.Functional.Vectors;
with SPARK.Containers.Functional.Infinite_Sequences;

procedure Main with SPARK_Mode is

   procedure Test_Sets with Global => null is
      package My_Sets is new SPARK.Containers.Functional.Sets (String);
      X : My_Sets.Set := ["foo", "bar", "foobar"];
   begin
      --  Here we do not know precisely the length of X
      pragma Assert (My_Sets.Length (X) = 3);
      pragma Assert (My_Sets.Contains (X, "foo"));
      pragma Assert (My_Sets.Contains (X, "bar"));
      pragma Assert (My_Sets.Contains (X, "foobar"));
   end Test_Sets;

   procedure Test_Maps with Global => null is
      package My_Maps is new SPARK.Containers.Functional.Maps (Integer, String);
      X : My_Maps.Map := [1 => "one", 2 => "two", 3 => "three"];
   begin
      pragma Assert (My_Maps.Length (X) = 3);
      pragma Assert (My_Maps.Has_Key (X, 1) and My_Maps.Get (X, 1) = "one");
      pragma Assert (My_Maps.Has_Key (X, 2) and My_Maps.Get (X, 2) = "two");
      pragma Assert (My_Maps.Has_Key (X, 3) and My_Maps.Get (X, 3) = "three");
   end Test_Maps;

   procedure Test_Multisets with Global => null is
      package My_Msets is new SPARK.Containers.Functional.Multisets (Integer);
      X : My_Msets.Multiset := [1 => 2, 3 => 1];
   begin
      --  Here we do not know the cardinality of X
      pragma Assert (My_Msets.Cardinality (X) = 3);  --  unprovable for now
      pragma Assert (My_Msets.Nb_Occurence (X, 1) = 2);
      pragma Assert (My_Msets.Nb_Occurence (X, 2) = 0);
      pragma Assert (My_Msets.Nb_Occurence (X, 3) = 1);
   end Test_Multisets;

   procedure Test_Vectors with Global => null is
      package My_Vectors is new SPARK.Containers.Functional.Vectors (Natural, String);
      X : My_Vectors.Sequence := ["foo", "bar", "foobar"];
   begin
      pragma Assert (My_Vectors.Last (X) = 2);
      pragma Assert (My_Vectors.Get (X, 0) = "foo");
      pragma Assert (My_Vectors.Get (X, 1) = "bar");
      pragma Assert (My_Vectors.Get (X, 2) = "foobar");
   end Test_Vectors;

   procedure Test_Sequences with Global => null is
      package My_Seqs is new SPARK.Containers.Functional.Infinite_Sequences (String);
      X : My_Seqs.Sequence := ["foo", "bar", "foobar"];
   begin
      pragma Assert (My_Seqs.Last (X) = 3);
      pragma Assert (My_Seqs.Get (X, 1) = "foo");
      pragma Assert (My_Seqs.Get (X, 2) = "bar");
      pragma Assert (My_Seqs.Get (X, 3) = "foobar");
   end Test_Sequences;

begin
   Test_Sets;
   Test_Maps;
   Test_Multisets;
   --  Test_Vectors; --  For some reason, even a call to Empty_Sequence crashes when assertions are enabled in the container library
   Test_Sequences;
end Main;
