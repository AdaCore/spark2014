with Ada.Unchecked_Conversion;
with System;
package body Crash
is
   pragma SPARK_Mode (On);

   type Byte is mod 256;
   type Int32 is mod 2 ** 32;

   type Block is array (0 .. 7) of Boolean;
   pragma Pack (Block);

   type Colour is record
      R : Byte;
      G : Byte;
      B : Byte;
      A : Byte;
   end record;

   function Cast is new Ada.Unchecked_Conversion (Int32, Colour);

   function Cast is new Ada.Unchecked_Conversion (Byte, Block);

   procedure Test_01 (I : Int32;
                      R : out Byte)
   with Global  => null,
        Depends => (R => I)
   is
   begin

      R := Cast (I).R;

   end Test_01;

   procedure Test_02 (C : Colour;
                      B : out Boolean)
   with Global  => null,
        Depends => (B => C)
   is
   begin

      B := Cast (C.A) (7);

   end Test_02;

end Crash;
