with Ada.Unchecked_Conversion;
with Interfaces; use Interfaces;

package body Mixed_Order with SPARK_Mode is
   procedure Check_One_Word is
      type Halves is array (1 .. 2) of Unsigned_16
        with Component_Size => 16, Size => 32, Alignment => 4;
      function Decode is new Ada.Unchecked_Conversion (Halves, Unsigned_32);
   begin
      pragma Assert (Decode ((16#1234#, 16#5678#)) = 16#1234_5678#);
   end Check_One_Word;

   procedure Check_Two_Words is
      type Words is array (1 .. 2) of Unsigned_32
        with Component_Size => 32, Size => 64, Alignment => 8;

      --  This conversion spans two words, and the target orders words and
      --  bytes differently.

      function Decode is new Ada.Unchecked_Conversion (Words, Unsigned_64);
      pragma Unreferenced (Decode);
   begin
      null;
   end Check_Two_Words;
end Mixed_Order;
