package H_3 with SPARK_Mode is
   type Root is tagged private;

   function Create return Root;

   type Grand_Child is new Root with private;
private
   pragma SPARK_Mode (Off);
   type Root is tagged null record;

   function Create return Root is ((null record));

   type Child is new Root with record
      F : Boolean;
   end record;

   function Create return Child is ((F => True));

   type Grand_Child is new Child with null record;
end H_3;
