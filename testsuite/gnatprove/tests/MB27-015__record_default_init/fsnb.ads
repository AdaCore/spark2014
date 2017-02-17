--  Like FSB, but NO BODIES available for analysis
package FSNB
  with SPARK_Mode => On
is
   S : Integer := 1;

   --  Supporting functions that DO NOT have a body

   --  No Global aspect, body might ref vars, but
   --  no way of knowing...
   function F5 (X, Y : in Integer) return Integer;

   --  Global aspect, body does NOT ref vars
   function F6 (X, Y : in Integer) return Integer
     with Global => null;

   --  Global aspect, body DOES ref vars
   function F7 (X, Y : in Integer) return Integer
     with Global => S;

end FSNB;
