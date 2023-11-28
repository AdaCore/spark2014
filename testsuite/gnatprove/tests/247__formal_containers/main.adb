with SPARK.Containers.Types; use SPARK.Containers.Types;
with SPARK.Containers.Formal.Doubly_Linked_Lists;
with SPARK.Containers.Formal.Hashed_Maps;
with SPARK.Containers.Formal.Hashed_Sets;
with SPARK.Containers.Formal.Ordered_Maps;
with SPARK.Containers.Formal.Ordered_Sets;
with SPARK.Containers.Formal.Vectors;

procedure Main with SPARK_Mode is
   package Nested is
      function Hash (X : Natural) return Hash_Type is
        (Hash_Type (X))
      with Global => null;
   end Nested;
   use Nested;

   procedure Test_Lists with Global => null is
      package My_Lists is new SPARK.Containers.Formal.Doubly_Linked_Lists (Integer);
      use My_Lists;
      X : My_Lists.List := [1, 2, 3];
   begin
      pragma Assert (Length (X) = 3);
      pragma Assert (First_Element (X) = 1);
      pragma Assert (Element (X, Next (X, First (X))) = 2);
      pragma Assert (Element (X, Next (X, Next (X, First (X)))) = 3);
   end Test_Lists;

   procedure Test_Hashed_Maps (K : Natural) with Global => null is
      package My_Maps is new SPARK.Containers.Formal.Hashed_Maps (Natural, Integer, Hash);
      use My_Maps;
      X : My_Maps.Map := [1 => 1, 2 => 2, 3 => 3];
   begin
      pragma Assert (Length (X) = 3);
      pragma Assert (Contains (X, K) = (K in 1 .. 3));
      pragma Assert (if Contains (X, K) then Element (X, K) = K);
   end Test_Hashed_Maps;

   procedure Test_Hashed_Sets (E : Natural) with Global => null is
      package My_Sets is new SPARK.Containers.Formal.Hashed_Sets (Natural, Hash);
      use My_Sets;
      X : My_Sets.Set := [1, 2, 3];
   begin
      pragma Assert (Length (X) = 3);
      pragma Assert (Contains (X, E) = (E in 1 .. 3));
   end Test_Hashed_Sets;

   procedure Test_Ordered_Maps with Global => null is
      package My_Maps is new SPARK.Containers.Formal.Ordered_Maps (Integer, Integer);
      use My_Maps;
      X : My_Maps.Map := [1 => 1, 2 => 2, 3 => 3];
   begin
      pragma Assert (Length (X) = 3);
      pragma Assert (First_Key (X) = 1);
      pragma Assert (Key (X, Next (X, First (X))) = 2);
      pragma Assert (Key (X, Next (X, Next (X, First (X)))) = 3);
      pragma Assert (First_Element (X) = 1);
      pragma Assert (Element (X, Next (X, First (X))) = 2);
      pragma Assert (Element (X, Next (X, Next (X, First (X)))) = 3);
   end Test_Ordered_Maps;

   procedure Test_Ordered_Sets with Global => null is
      package My_Sets is new SPARK.Containers.Formal.Ordered_Sets (Integer);
      use My_Sets;
      X : My_Sets.Set := [1, 2, 3];
   begin
      pragma Assert (Length (X) = 3);
      pragma Assert (First_Element (X) = 1);
      pragma Assert (Element (X, Next (X, First (X))) = 2);
      pragma Assert (Element (X, Next (X, Next (X, First (X)))) = 3);
   end Test_Ordered_Sets;

   procedure Test_Vectors with Global => null is
      package My_Vectors is new SPARK.Containers.Formal.Vectors (Positive, Integer);
      use My_Vectors;
      X : My_Vectors.Vector := [1, 2, 3];
   begin
      pragma Assert (Length (X) = 3);
      pragma Assert (Element (X, 1) = 1);
      pragma Assert (Element (X, 2) = 2);
      pragma Assert (Element (X, 3) = 3);
   end Test_Vectors;

begin
   Test_Lists;
   Test_Hashed_Maps (1);
   Test_Hashed_Sets (1);
   Test_Ordered_Maps;
   Test_Ordered_Sets;
   Test_Vectors;
end Main;
