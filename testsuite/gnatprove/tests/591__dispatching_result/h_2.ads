package H_2 with SPARK_Mode is
   type Root is tagged private;

   function Create return Root;

   type Child is tagged private;
private
   pragma SPARK_Mode (Off);

   type Root is tagged record
      F : Boolean;
   end record;

   function Create return Root is ((F => True));

   type Child is new Root with null record;
end H_2;
