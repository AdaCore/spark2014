package Types is

   type Byte is mod 2 ** 8;
   type Bytes is array (Positive range <>) of Byte;

   procedure Convert_To_U13 (Offset : Natural)
   with Pre => Offset <= Natural'Last - 13;

end Types;
