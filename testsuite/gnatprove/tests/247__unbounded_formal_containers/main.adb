with SPARK.Containers.Types; use SPARK.Containers.Types;
with SPARK.Containers.Formal.Unbounded_Doubly_Linked_Lists;
with SPARK.Containers.Formal.Unbounded_Hashed_Maps;
with SPARK.Containers.Formal.Unbounded_Hashed_Sets;
with SPARK.Containers.Formal.Unbounded_Ordered_Maps;
with SPARK.Containers.Formal.Unbounded_Ordered_Sets;
with SPARK.Containers.Formal.Unbounded_Vectors;

procedure Main with SPARK_Mode is
   package Nested is
      function Hash (X : Natural) return Hash_Type is
        (Hash_Type (X))
      with Global => null;
   end Nested;
   use Nested;

   procedure Test_Unbounded_Lists with Global => null is
      package My_Lists is new SPARK.Containers.Formal.Unbounded_Doubly_Linked_Lists (String);
      use My_Lists;
      X : My_Lists.List := ["foo", "bar", "foobar"];
   begin
      pragma Assert (Length (X) = 3);
      pragma Assert (First_Element (X) = "foo");
      pragma Assert (Element (X, Next (X, First (X))) = "bar");
      pragma Assert (Element (X, Next (X, Next (X, First (X)))) = "foobar");
   end Test_Unbounded_Lists;

   procedure Test_Unbounded_Hashed_Maps (K : Natural) with Global => null is
      package My_Maps is new SPARK.Containers.Formal.Unbounded_Hashed_Maps (Natural, String, Hash);
      use My_Maps;
      X : My_Maps.Map := [1 => "foo", 2 => "bar", 3 => "foobar"];
   begin
      pragma Assert (Length (X) = 3);
      pragma Assert (Contains (X, K) = (K in 1 .. 3));
      pragma Assert (Element (X, 1) = "foo");
      pragma Assert (Element (X, 2) = "bar");
      pragma Assert (Element (X, 3) = "foobar");
   end Test_Unbounded_Hashed_Maps;

   procedure Test_Unbounded_Hashed_Sets (E : Natural) with Global => null is
      package My_Sets is new SPARK.Containers.Formal.Unbounded_Hashed_Sets (Natural, Hash);
      use My_Sets;
      X : My_Sets.Set := [1, 2, 3];
   begin
      pragma Assert (Length (X) = 3);
      pragma Assert (Contains (X, E) = (E in 1 .. 3));
   end Test_Unbounded_Hashed_Sets;

   procedure Test_Unbounded_Ordered_Maps with Global => null is
      package My_Maps is new SPARK.Containers.Formal.Unbounded_Ordered_Maps (Integer, String);
      use My_Maps;
      X : My_Maps.Map := [1 => "foo", 2 => "bar", 3 => "foobar"];
   begin
      pragma Assert (Length (X) = 3);
      pragma Assert (First_Key (X) = 1);
      pragma Assert (Key (X, Next (X, First (X))) = 2);
      pragma Assert (Key (X, Next (X, Next (X, First (X)))) = 3);
      pragma Assert (First_Element (X) = "foo");
      pragma Assert (Element (X, Next (X, First (X))) = "bar");
      pragma Assert (Element (X, Next (X, Next (X, First (X)))) = "foobar");
   end Test_Unbounded_Ordered_Maps;

   procedure Test_Unbounded_Ordered_Sets with Global => null is
      package My_Sets is new SPARK.Containers.Formal.Unbounded_Ordered_Sets (Integer);
      use My_Sets;
      X : My_Sets.Set := [1, 2, 3];
   begin
      pragma Assert (Length (X) = 3);
      pragma Assert (First_Element (X) = 1);
      pragma Assert (Element (X, Next (X, First (X))) = 2);
      pragma Assert (Element (X, Next (X, Next (X, First (X)))) = 3);
   end Test_Unbounded_Ordered_Sets;

   procedure Test_Unbounded_Vectors with Global => null is
      package My_Vectors is new SPARK.Containers.Formal.Unbounded_Vectors (Positive, String);
      use My_Vectors;
      X : My_Vectors.Vector := ["foo", "bar", "foobar"];
   begin
      pragma Assert (Length (X) = 3);
      pragma Assert (Element (X, 1) = "foo");
      pragma Assert (Element (X, 2) = "bar");
      pragma Assert (Element (X, 3) = "foobar");
   end Test_Unbounded_Vectors;

begin
   Test_Unbounded_Lists;
   Test_Unbounded_Hashed_Maps (1);
   Test_Unbounded_Hashed_Sets (1);
   Test_Unbounded_Ordered_Maps;
   Test_Unbounded_Ordered_Sets;
   Test_Unbounded_Vectors;
end Main;
