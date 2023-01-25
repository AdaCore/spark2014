with HO_Sets; use HO_Sets;
with SPARK.Big_Integers; use SPARK.Big_Integers;

procedure Use_Sets with SPARK_Mode is
   use HO_Sets.My_Sets;

   --  Two properties which are proved because of the lemmas of Count

   procedure Prove_Count_Add_Gen (S : Set; E : Integer; F : not null access function (E : Integer) return Boolean) with
     Ghost,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Pre  => not Contains (S, E),
     Post => Count (Add (S, E), F) = Count (S, F) + (if F (E) then Big_Integer'(1) else 0);

   procedure Prove_Count_Add_Gen (S : Set; E : Integer; F : not null access function (E : Integer) return Boolean) is null;

   procedure Prove_Count_Remove_Gen (S : Set; E : Integer; F : not null access function (E : Integer) return Boolean) with
     Ghost,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Pre  => Contains (S, E),
     Post => Count (Remove (S, E), F) = Count (S, F) - (if F (E) then Big_Integer'(1) else 0);

   procedure Prove_Count_Remove_Gen (S : Set; E : Integer; F : not null access function (E : Integer) return Boolean) is null;

   --  Specialization of Count

   function Count_Values_In_Range (S : Set; A, B : Integer) return Big_Integer with
     Post => Count_Values_In_Range'Result <= Length (S);

   function Count_Values_In_Range (S : Set; A, B : Integer) return Big_Integer is
      function In_Range (E : Integer) return Boolean is (E in A .. B);

      function Count_In_Range (S : Set) return Big_Integer is
        (Count (S, In_Range'Access));

      --  Check that we can prove the same properties on the specialization

      procedure Prove_Count_Add_In_Range (S : Set; E : Integer) with
        Ghost,
        Pre  => not Contains (S, E),
        Post => Count_In_Range (Add (S, E)) = Count_In_Range (S) + (if E in A .. B then Big_Integer'(1) else 0);

      procedure Prove_Count_Add_In_Range (S : Set; E : Integer) is null;

      procedure Prove_Count_Remove_In_Range (S : Set; E : Integer) with
        Ghost,
        Pre  => Contains (S, E),
        Post => Count_In_Range (Remove (S, E)) = Count_In_Range (S) - (if E in A .. B then Big_Integer'(1) else 0);

      procedure Prove_Count_Remove_In_Range (S : Set; E : Integer) is null;
   begin
      return Count_In_Range (S);
   end Count_Values_In_Range;
begin
   null;
end Use_Sets;
