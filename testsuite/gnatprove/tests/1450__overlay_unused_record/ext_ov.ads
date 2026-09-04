--  The types below come from a unit which is not the one being analyzed, so
--  they are candidates for the "unused record" abstraction. Inner is only
--  ever reached as a subcomponent of Outer, so nothing touches its fields.

package Ext_Ov with SPARK_Mode is
   type U8 is mod 2 ** 8 with Size => 8;

   type Arr is array (1 .. 8) of U8 with Object_Size => 64, Alignment => 1;

   type Inner is record
      P : Arr;
   end record with Size => 64, Object_Size => 64, Alignment => 1;
   for Inner use record
      P at 0 range 0 .. 63;
   end record;

   type Outer is record
      K : Inner;
   end record with Size => 64, Object_Size => 64, Alignment => 1;
   for Outer use record
      K at 0 range 0 .. 63;
   end record;

   type Buf is array (1 .. 8) of U8
     with Size => 64, Object_Size => 64, Alignment => 1;
end Ext_Ov;
