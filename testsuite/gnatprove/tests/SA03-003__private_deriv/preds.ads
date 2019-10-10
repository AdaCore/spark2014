package Preds with SPARK_Mode is

   type Root is tagged record
      F : Integer := 1;
   end record;

   type Child is new Root with record
      G : Integer;
   end record;

   type Grand_Grand_Child is new Root with private;
private
   pragma SPARK_Mode (Off);

   type Bad is access all Integer;
   CC : constant Bad := new Integer'(40);

   type Grand_Child is new Child with record
      H : Integer;
   end record;

   type Grand_Grand_Child is new Grand_Child with record
      I : Integer;
   end record;
end Preds;
