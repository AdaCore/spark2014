with Interfaces;
package Byte_Order with SPARK_Mode is
   subtype Byte is Interfaces.Unsigned_8;
   subtype Word is Interfaces.Unsigned_16;
   type Pair is array (1 .. 2) of Byte
     with Component_Size => 8, Size => 16, Alignment => 2;
   function First_Word return Word;
   procedure Check;
   procedure Check_Reversed;
   procedure Check_Encode;
   procedure Check_Packed_Nibbles;
   procedure Check_Partial_Storage_Unit;
end Byte_Order;
