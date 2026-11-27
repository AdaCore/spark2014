with Ada.Unchecked_Conversion;
package body Byte_Order with SPARK_Mode is
   use type Word;
   function Decode is new Ada.Unchecked_Conversion (Pair, Word);
   function Encode is new Ada.Unchecked_Conversion (Word, Pair);
   function First_Word return Word is (Decode ((16#12#, 16#34#)));
   procedure Check is
   begin
      pragma Assert (First_Word = 16#1234#);
   end Check;

   procedure Check_Reversed is
   begin
      pragma Assert (First_Word = 16#3412#);
   end Check_Reversed;

   procedure Check_Encode is
   begin
      pragma Assert (Encode (16#1234#) = (16#12#, 16#34#));
   end Check_Encode;

   procedure Check_Packed_Nibbles is
      type Nibble is mod 2 ** 4 with Size => 4;
      type Nibbles is array (1 .. 2) of Nibble
        with Component_Size => 4, Size => 8, Alignment => 1;
      function Decode_Nibbles is new Ada.Unchecked_Conversion (Nibbles, Byte);
      use type Byte;
   begin
      --  The first element occupies the high nibble on this target.

      pragma Assert (Decode_Nibbles ((1, 2)) = 16#12#);
   end Check_Packed_Nibbles;

   procedure Check_Partial_Storage_Unit is
      type Nibble is mod 2 ** 4 with Size => 4;
      type Nibbles is array (1 .. 3) of Nibble
        with Component_Size => 4, Size => 12, Alignment => 2;
      type Twelve_Bits is mod 2 ** 12 with Size => 12, Alignment => 2;

      --  A 12-bit value ends in a partial storage unit.

      function Decode is new Ada.Unchecked_Conversion (Nibbles, Twelve_Bits);
      pragma Unreferenced (Decode);
   begin
      null;
   end Check_Partial_Storage_Unit;
end Byte_Order;
