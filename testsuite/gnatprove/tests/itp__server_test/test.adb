package body Test
is
   type Unsigned_Byte is range 0..255;
   type Byte is range -128..127;

   --  Parity of an integer. Easy example which allows to
   --  easily show induction
   function Parity (A: Unsigned_Byte) return Unsigned_Byte
     with
       Pre => A > 0,
       Post => (for some X in Unsigned_Byte'Range =>
                  A = X + X or else A = X + X + 1)
   is
   begin
      return A;
   end Parity;

end Test;
