package body Bitset with SPARK_Mode
is

   -------------------------------------------------------------------------

   function Bit_Clear
     (Value : Word64;
      Pos   : Word64_Pos)
      return Word64
   is
      Mask : Word64;
   begin
      Mask := not (2 ** Natural (Pos));
      return Value and Mask;
   end Bit_Clear;

   -------------------------------------------------------------------------

   function Bit_Set
     (Value : Word64;
      Pos   : Word64_Pos)
      return Word64
   is
      Res : Word64 := Value;
   begin
      pragma Assert (2 ** Natural (Pos) in Word64);
      pragma Assert (2 ** Natural (Pos) > 0);
      Res := Res or 2 ** Natural (Pos);
      pragma Assert ((Res or 2 ** Natural (Pos)) /= 0);
      return Res;
   end Bit_Set;

   -------------------------------------------------------------------------

   function Bit_Test
     (Value : Word64;
      Pos   : Word64_Pos)
      return Boolean
   is
      Mask : Word64;
   begin
      Mask := 2 ** Natural (Pos);
      return ((Value and Mask) /= 0);
   end Bit_Test;

end Bitset;
