with Interfaces;

use type Interfaces.Unsigned_32;
use type Interfaces.Unsigned_64;

package Test
is

   subtype Big_Int_Range is Natural range Natural'First .. Natural'Last - 1;

   type Big_Int is array (Big_Int_Range range <>) of Interfaces.Unsigned_32;

   function Bit_Set
     (A       : Big_Int;
      A_First : Natural;
      I       : Interfaces.Unsigned_64)
     return Boolean
     with
       Pre =>
         A_First in A'Range and then
         I / 32 <= Interfaces.Unsigned_64 (A'Last - A_First),
       Post =>
         Bit_Set'Result =
         ((A (A_First + Natural (I / 32)) and
           2 ** (Natural (I mod 32))) /= 0);

end Test;
