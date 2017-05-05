package Tagged_Types with SPARK_Mode is
   type Root is tagged record
      I : Integer;
   end record;

   function F (X : Root) return Integer is (X.I);

   function G (X : Root) return Integer is (F (Root'Class (X))) with
   Extensions_Visible;

   type Child is new Root with record
      J : Integer;
   end record;

   function F (X : Child) return Integer is (X.J);
end Tagged_Types;
