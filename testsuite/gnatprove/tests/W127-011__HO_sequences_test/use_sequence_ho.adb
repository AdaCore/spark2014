with SPARK.Big_Integers; use SPARK.Big_Integers;
with SPARK.Containers.Functional.Infinite_Sequences;
with SPARK.Containers.Functional.Infinite_Sequences.Higher_Order;

procedure Use_Sequence_HO with SPARK_Mode is

   --  Check that properties can be proven on HO functions on Sequences

   package My_Sequences is new SPARK.Containers.Functional.Infinite_Sequences
     (String);
   use My_Sequences;

   package HO is new My_Sequences.Higher_Order;
   use HO;

   package Test_Count is
      function Starts_With_Z (S : String) return Boolean is
        (S'Length > 0 and then S (S'First) = 'Z');

      function Add_Zero (S : Sequence) return Sequence is
        (Add (S, "ZERO"))
          with
          Post => Count (Add_Zero'Result, Starts_With_Z'Access) =
            Count (S, Starts_With_Z'Access) + 1;

      function Add_One (S : Sequence) return Sequence is
        (Add (S, "ONE"))
          with
          Post => Count (Add_One'Result, Starts_With_Z'Access) =
            Count (S, Starts_With_Z'Access);
   end Test_Count;

   package Test_Filter is
      function Starts_With_Z (S : String) return Boolean is
        (S'Length > 0 and then S (S'First) = 'Z');

      function Add_Zero (S : Sequence) return Sequence with
          Post => Filter (Add_Zero'Result, Starts_With_Z'Access) =
            Add (Filter (S, Starts_With_Z'Access), "ZERO");

      function Add_One (S : Sequence) return Sequence is
        (Add (S, "ONE"))
          with
          Post => Filter (Add_One'Result, Starts_With_Z'Access) =
            Filter (S, Starts_With_Z'Access);
   end Test_Filter;

   package body Test_Filter is

      function Add_Zero (S : Sequence) return Sequence is
         Res : constant Sequence := Add (S, "ZERO");
      begin
         pragma Assert (Filter (S, Starts_With_Z'Access) = Filter (Res, Length (S), Starts_With_Z'Access));
         return Res;
      end Add_Zero;
   end Test_Filter;

   package Test_Sum is
      function Value (S : String) return Big_Integer is
        (To_Big_Integer (Integer (S'Length)));

      function Add_Zero (S : Sequence) return Sequence is
        (Add (S, "ZERO"))
          with
          Post => Sum (Add_Zero'Result, Value'Access) =
            Sum (S, Value'Access) + 4;

      function Add_One (S : Sequence) return Sequence is
        (Add (S, "ONE"))
          with
          Post => Sum (Add_One'Result, Value'Access) =
            Sum (S, Value'Access) + 3;
   end Test_Sum;

   package Test_Transform is
      function F (S : String) return String is
        ("New_" & S (S'First .. Natural'Min (S'Last, Natural'Last - 4)));

      function Add_Zero (S : Sequence) return Sequence is
        (Add (S, "ZERO"))
          with
          Post => Transform (Add_Zero'Result, F'Access) = Add (Transform (S, F'Access), "New_ZERO");
   end Test_Transform;

   package Test_Create is
      function F (I : Big_Positive) return String is
        ("Value");

      procedure Lemma_Add_Item (I : Positive) with
        Ghost,
        Post => Create (To_Big_Integer (I), F'Access) = Add (Create (To_Big_Integer (I - 1), F'Access), "Value");
      procedure Lemma_Add_Item (I : Positive) is null;
   end Test_Create;
begin
   null;
end Use_Sequence_HO;
