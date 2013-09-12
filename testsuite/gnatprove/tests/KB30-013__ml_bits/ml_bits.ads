with System;
package Ml_Bits is pragma SPARK_Mode (On);

   type T_Bit is range 0 .. 1;
   for T_Bit'Size use 1;

   type T_4bit is range 0 .. 15;
   for T_4Bit'Size use 4;

   subtype T_Int32 is Integer;
   subtype T_Nat32 is Natural;

   type T_Bit_Buffer is array (T_Nat32 range <>) of T_Bit;
   pragma Pack (T_Bit_Buffer);

   type T_4bit_Buffer is new T_Bit_Buffer(0..3);
   pragma Pack (T_4bit_Buffer);
   for T_4bit_Buffer'Size use 4;

  function Buffer_4bit_To_Int32 (X : in T_4bit_Buffer) return T_Int32;

end Ml_Bits;
