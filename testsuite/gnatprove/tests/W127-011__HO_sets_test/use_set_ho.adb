with SPARK.Big_Integers; use SPARK.Big_Integers;
with SPARK.Containers.Functional.Sets;
with SPARK.Containers.Functional.Sets.Higher_Order;

procedure Use_Set_HO with SPARK_Mode is

   --  Check that properties can be proven on HO functions on sets

   package My_Sets is new SPARK.Containers.Functional.Sets
     (Integer);
   use My_Sets;

   package HO is new My_Sets.Higher_Order;
   use HO;

   package Test_Count is
      function Is_Even (X : Integer) return Boolean is
        (X mod 2 = 0);

      function Add_Zero (S : Set) return Set is
        (Add (S, 0))
          with Pre => not Contains (S, 0),
          Post => Count (Add_Zero'Result, Is_Even'Access) =
            Count (S, Is_Even'Access) + 1;

      function Add_One (S : Set) return Set is
        (Add (S, 1))
          with Pre => not Contains (S, 1),
          Post => Count (Add_One'Result, Is_Even'Access) =
            Count (S, Is_Even'Access);
   end Test_Count;

   package Test_Filter is
      function Is_Even (X : Integer) return Boolean is
        (X mod 2 = 0);

      function Add_Zero (S : Set) return Set is
        (Add (S, 0))
          with Pre => not Contains (S, 0),
          Post => Filter (Add_Zero'Result, Is_Even'Access) =
            Add (Filter (S, Is_Even'Access), 0);

      function Add_One (S : Set) return Set is
        (Add (S, 1))
          with Pre => not Contains (S, 1),
          Post => Filter (Add_One'Result, Is_Even'Access) =
            Filter (S, Is_Even'Access);
   end Test_Filter;

   package Test_Sum is
      function Value (X : Integer) return Big_Integer is
        (To_Big_Integer (X));

      function Add_Zero (S : Set) return Set is
        (Add (S, 0))
          with Pre => not Contains (S, 0),
          Post => Sum (Add_Zero'Result, Value'Access) =
            Sum (S, Value'Access);

      function Add_One (S : Set) return Set is
        (Add (S, 1))
          with Pre => not Contains (S, 1),
          Post => Sum (Add_One'Result, Value'Access) =
            Sum (S, Value'Access) + 1;
   end Test_Sum;

   package Test_Transform_Distinct is
      function F (X : Integer) return Integer is
        (if X = Integer'Last then Integer'First else X + 1);

      function Add_Zero (S : Set) return Set is
        (Add (S, 0))
          with Pre => not Contains (S, 0),
          Post => Transform_Distinct (Add_Zero'Result, F'Access) = Add (Transform_Distinct (S, F'Access), 1);
   end Test_Transform_Distinct;

   package Test_Transform is
      function F (X : Integer) return Integer is
        (X mod 2);

      function Add_Zero (S : Set) return Set is
        (Add (S, 0))
          with Pre => not Contains (S, 0),
          Post => Transform (S, F'Access) <= Transform (Add_Zero'Result, F'Access)
          and then Contains (Transform (Add_Zero'Result, F'Access), 0);
   end Test_Transform;

   package Test_Create_Distinct is
      function F (I : Big_Positive) return Integer is
        (if In_Range (I, 1, To_Big_Integer (Integer'Last)) then To_Integer (I) else 0);

      procedure Lemma_Add_Item (I : Positive) with
        Ghost,
        Post => Create_Distinct (To_Big_Integer (I), F'Access) = Add (Create_Distinct (To_Big_Integer (I - 1), F'Access), I);
      procedure Lemma_Add_Item (I : Positive) is null;
   end Test_Create_Distinct;

   package Test_Create is
      function F (I : Big_Positive) return Integer is
        (if In_Range (I, 1, To_Big_Integer (Integer'Last)) then To_Integer (I mod 2) else 0);

      procedure Lemma_Add_Item (I : Positive) with
        Ghost,
        Post => Create (To_Big_Integer (I - 1), F'Access) <= Create (To_Big_Integer (I), F'Access)
        and then Contains (Create (To_Big_Integer (I), F'Access), I mod 2);
      procedure Lemma_Add_Item (I : Positive) is null;
   end Test_Create;
begin
   null;
end Use_Set_HO;
