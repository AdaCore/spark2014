package body Over is
   function F (X : Integer) return Integer
   is
   begin
      return X;
   end F;

   function F (Z : My_Int) return My_Int
   is
   begin
      return 1;
   end F;

   procedure G is
      Z : Integer := 2;
      Y : Integer := F (Z);
   begin
      pragma Assert (Y = 2);
   end G;
end Over;
