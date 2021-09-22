package Ren is

   function F (X : Integer) return Integer is (X);

   function RF (X : Integer) return Integer with Pre => X > 0;
   function RF (X : Integer) return Integer renames F;

   pragma Assert (F(42) = 42);
   pragma Assert (RF(42) = 42);

end Ren;
