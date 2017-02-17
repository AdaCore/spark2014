package body FSB
  with SPARK_Mode => On
is
   --  Supporting functions that DO have a body

   -- No Global aspect, body does NOT ref vars
   function F1 (X, Y : in Integer) return Integer
   is
   begin
      return X + Y;
   end F1;

   -- No Global aspect, body DOES ref vars
   function F2 (X, Y : in Integer) return Integer
   is
   begin
      return X + Y + S;
   end F2;

   -- Global aspect, body does NOT ref vars
   function F3 (X, Y : in Integer) return Integer
   is
   begin
      return X + Y;
   end F3;

   -- Global aspect, body DOES ref vars
   function F4 (X, Y : in Integer) return Integer
   is
   begin
      return X + Y + S;
   end F4;


end FSB;
