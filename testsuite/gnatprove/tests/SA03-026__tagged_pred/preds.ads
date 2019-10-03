package Preds with SPARK_Mode is

   type Root is tagged record
      F : Integer := 1;
   end record;

   type Child is new Root with record
      G : Integer;
   end record with Predicate => Child.F > 12;

   type Grand_Grand_Child is new Root with private with
     Dynamic_Predicate => Grand_Grand_Child.F < 40;
private

   type Grand_Child is new Child with record
      H : Integer;
   end record with Predicate => Grand_Child.F < 10;

   type Grand_Grand_Child is new Grand_Child with record
      I : Integer;
   end record with Predicate => Grand_Grand_Child.F < 40;
end Preds;
