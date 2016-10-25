package body Test
is

   function Bit_Set
     (A       : Big_Int;
      A_First : Natural;
      I       : Interfaces.Unsigned_64)
     return Boolean
   is
   begin
      return
        (A (A_First + Natural (I / 32)) and
         2 ** (Natural (I mod 32))) /= 0;
   end Bit_Set;

end Test;
