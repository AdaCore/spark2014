package Parent_Types with SPARK_Mode is
   type Root is record
      F : Positive;
   end record;
   for Root use record
      F at 0 range 0 .. 31;
   end record;

   type Middle is new Root;
   for Middle use record
      F at 0 range 0 .. 63;
   end record;

   type Leaf is new Middle;
end Parent_Types;
