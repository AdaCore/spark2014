package Preds with SPARK_Mode is

   type Root is tagged record
      F : Integer := 1;
   end record;

   type Child is new Root with record
      G : Integer;
   end record with Predicate => Child.F <= Child.G;

   type Bad is private;
private
   pragma SPARK_Mode (Off);

   type Bad is access all Integer;
end Preds;
