package Q
  with SPARK_Mode
is
   type T is record
      X : Integer;
   end record
     with Size => 32;

   subtype S is T;

   pragma Assert (T'Size = 32);
   pragma Assert (S'Size = 32);

   -- one level generic

   generic
      type Data is private;
   package Gen is
      type T is record
         X : Data;
      end record;
      subtype S is T;
   end;

   package Pack is new Gen (Integer);

   pragma Assert (Pack.T'Size = 32);
   pragma Assert (Pack.S'Size = 32);

   -- two levels generic

   generic
      type Data is private;
   package Gen2 is
      package Pack is new Gen (Data);
   end;

   package Pack2 is new Gen2 (Integer);

   pragma Assert (Pack2.Pack.T'Size = 32);
   pragma Assert (Pack2.Pack.S'Size = 32);

   -- from with'ed unit

   pragma Assert (Q.T'Size = 32);
   pragma Assert (Q.S'Size = 32);

   pragma Assert (Q.Pack.T'Size = 32);
   pragma Assert (Q.Pack.S'Size = 32);

   pragma Assert (Q.Pack2.Pack.T'Size = 32);
   pragma Assert (Q.Pack2.Pack.S'Size = 32);

end Q;
