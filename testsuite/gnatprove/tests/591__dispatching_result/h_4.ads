package H_4 with SPARK_Mode is
   type Root is tagged private;

   type Child is new Root with private;

   function Create return Child;

   type Grand_Child is new Root with private;
private
   pragma SPARK_Mode (Off);
   type Root is tagged null record;

   type Child is new Root with record
      F : Boolean;
   end record;

   function Create return Child is ((F => True));

   type Grand_Child is new Child with null record;
end H_4;
