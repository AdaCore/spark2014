package Bar is
   type Half_Byte is mod 2 ** 4 with Size => 4;
   type Word is mod 2 ** 32 with Size => 32;
   type Word_Array is array (Integer range 0 .. 4) of Word;
   function Baz (Data : aliased Word_Array) return Word;
end Bar;
