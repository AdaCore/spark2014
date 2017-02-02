package Use_Quantif with SPARK_Mode is
   subtype Smaller is Integer range Integer'First + 1 .. Integer'Last;

   package Nested is
      One : constant Smaller;
      Lst : constant Integer;
      function Id (X : Integer) return Integer;
   private
      pragma SPARK_Mode (Off);
      function Id (X : Integer) return Integer is (X);
      One : constant Smaller := Id (Integer'First + 1);
      Lst : constant Integer := Id (Integer'Last);
   end Nested;

   First_Index : constant Smaller := Nested.One;
   Last_Index  : constant Integer := Nested.Lst;

   subtype Index_Type is Integer range First_Index .. Last_Index;

   procedure P (Fst, Lst : Index_Type) with
   Pre => Fst <= Lst;
end Use_Quantif;
