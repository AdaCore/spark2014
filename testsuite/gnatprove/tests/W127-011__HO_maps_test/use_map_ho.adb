with SPARK.Big_Integers; use SPARK.Big_Integers;
with SPARK.Containers.Functional.Maps;
with SPARK.Containers.Functional.Maps.Higher_Order;

procedure Use_Map_HO with SPARK_Mode is

   --  Check that properties can be proven on HO functions on Maps

   package My_Maps is new SPARK.Containers.Functional.Maps
     (Integer, String);
   use My_Maps;

   package HO is new My_Maps.Higher_Order;
   use HO;

   package Test_Count is
      function Is_Even (X : Integer; S : String) return Boolean is
        (X mod 2 = 0);

      function Add_Zero (M : Map) return Map is
        (Add (M, 0, "ZERO"))
          with Pre => not Has_Key (M, 0),
          Post => Count (Add_Zero'Result, Is_Even'Access) =
            Count (M, Is_Even'Access) + 1;

      function Add_One (M : Map) return Map is
        (Add (M, 1, "ONE"))
          with Pre => not Has_Key (M, 1),
          Post => Count (Add_One'Result, Is_Even'Access) =
            Count (M, Is_Even'Access);
   end Test_Count;

   package Test_Filter is
      function Is_Even (X : Integer; S : String) return Boolean is
        (X mod 2 = 0);

      function Add_Zero (M : Map) return Map is
        (Add (M, 0, "ZERO"))
          with Pre => not Has_Key (M, 0),
          Post => Filter (Add_Zero'Result, Is_Even'Access) =
            Add (Filter (M, Is_Even'Access), 0, "ZERO");

      function Add_One (M : Map) return Map is
        (Add (M, 1, "ONE"))
          with Pre => not Has_Key (M, 1),
          Post => Filter (Add_One'Result, Is_Even'Access) =
            Filter (M, Is_Even'Access);
   end Test_Filter;

   package Test_Sum is
      function Value (X : Integer; S : String) return Big_Integer is
        (To_Big_Integer (X));

      function Add_Zero (M : Map) return Map is
        (Add (M, 0, "ZERO"))
          with Pre => not Has_Key (M, 0),
          Post => Sum (Add_Zero'Result, Value'Access) =
            Sum (M, Value'Access);

      function Add_One (M : Map) return Map is
        (Add (M, 1, "ONE"))
          with Pre => not Has_Key (M, 1),
          Post => Sum (Add_One'Result, Value'Access) =
            Sum (M, Value'Access) + 1;
   end Test_Sum;

   function Is_Add (M1 : Map; K : Integer; E : String; M2 : Map) return Boolean is
     (M1 <= M2
      and then Keys_Included_Except (M2, M1, K)
      and then Has_Key (M2, K)
      and then Get (M2, K) = E);

   package Test_Transform is
      function F (X : Integer) return Integer is
        (if X = Integer'Last then Integer'First else X + 1);
      function F (S : String) return String is
        ("New_" & S (S'First .. Natural'Min (S'Last, Natural'Last - 4)));

      function Add_Zero (M : Map) return Map is
        (Add (M, 0, "ZERO"))
          with Pre => not Has_Key (M, 0),
          Post => Is_Add (Transform (M, F'Access, F'Access), 1, "New_ZERO", Transform (Add_Zero'Result, F'Access, F'Access));
   end Test_Transform;

   package Test_Transform_Element is
      function F (S : String) return String is
        ("New_" & S (S'First .. Natural'Min (S'Last, Natural'Last - 4)));

      function Add_Zero (M : Map) return Map is
        (Add (M, 0, "ZERO"))
          with Pre => not Has_Key (M, 0),
          Post => Is_Add (Transform_Element (M, F'Access), 0, "New_ZERO", Transform_Element (Add_Zero'Result, F'Access));
   end Test_Transform_Element;

   package Test_Create is
      function F (I : Big_Positive) return Integer is
        (if In_Range (I, 1, To_Big_Integer (Integer'Last)) then To_Integer (I) else 0);
      function F (I : Big_Positive) return String is
        ("Value");

      procedure Lemma_Add_Item (I : Positive) with
        Ghost,
        Post => Is_Add (Create (To_Big_Integer (I - 1), F'Access, F'Access), I, "Value", Create (To_Big_Integer (I), F'Access, F'Access));
      procedure Lemma_Add_Item (I : Positive) is null;
   end Test_Create;
begin
   null;
end Use_Map_HO;
