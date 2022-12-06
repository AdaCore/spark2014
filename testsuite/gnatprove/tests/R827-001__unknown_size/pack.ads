package Pack is

   type T is record
      X, Y : Integer;
   end record;

   X : T;

   pragma Assert (T'Size = 64);
   pragma Assert (T'Object_size = 64);
   pragma Assert (T'Value_size = 64);
   pragma Assert (X'Size = 64);

end Pack;
