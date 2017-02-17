package FSB
  with SPARK_Mode => On
is
   S : Integer := 1;

   --  Supporting functions that DO have a body

   -- No Global aspect, body does NOT ref vars
   function F1 (X, Y : in Integer) return Integer;

   -- No Global aspect, body DOES ref vars
   function F2 (X, Y : in Integer) return Integer;

   -- Global aspect, body does NOT ref vars
   function F3 (X, Y : in Integer) return Integer
     with Global => null;

   -- Global aspect, body DOES ref vars
   function F4 (X, Y : in Integer) return Integer
     with Global => S;

end FSB;
