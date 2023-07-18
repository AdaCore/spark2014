package body R
  with SPARK_Mode
is
   type Tb is record
      X : Integer;
   end record
     with Size => 32;

   subtype Sb is Tb;

   pragma Assert (Tb'Size = 32);
   pragma Assert (Sb'Size = 32);

   -- one level generic

   generic
      type Data is private;
   package Genb is
      type Tb is record
         X : Data;
      end record;
      subtype Sb is Tb;
   end;

   package Packb is new Genb (Integer);

   pragma Assert (Packb.Tb'Size = 32);
   pragma Assert (Packb.Sb'Size = 32);

   -- two levels generic

   generic
      type Data is private;
   package Gen2b is
      package Packb is new Genb (Data);
   end;

   package Pack2b is new Gen2b (Integer);

   pragma Assert (Pack2b.Packb.Tb'Size = 32);
   pragma Assert (Pack2b.Packb.Sb'Size = 32);

   procedure Test is null;

end R;
