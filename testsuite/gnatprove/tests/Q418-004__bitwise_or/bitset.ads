package Bitset with SPARK_Mode
is

   type Word64 is mod 2**64;
   for Word64'Size use 64;

   subtype Word64_Pos is Word64 range 0 .. 63;

   --  Test if bit at given position is set.
   function Bit_Test
     (Value : Word64;
      Pos   : Word64_Pos)
      return Boolean
   with
      Post => Bit_Test'Result = ((Value and 2 ** Natural (Pos)) /= 0);

   --  Set bit at given position.
   function Bit_Set
     (Value : Word64;
      Pos   : Word64_Pos)
      return Word64
   with
      Post => Bit_Test (Value => Bit_Set'Result, Pos => Pos) = True;

   --  Clear bit at given position.
   function Bit_Clear
     (Value : Word64;
      Pos   : Word64_Pos)
      return Word64
   with
      Post => Bit_Test (Value => Bit_Clear'Result, Pos => Pos) = False;

end Bitset;
