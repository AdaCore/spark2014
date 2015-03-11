package Foo
is
   type Word32 is mod 2 ** 32;
   type Word64 is mod 2 ** 64;

   subtype Big_Int_Range is Natural range Natural'First .. Natural'Last - 1;

   type Big_Int is array (Big_Int_Range range <>) of Word32;

   function Bit_Set
     (A       : Big_Int;
      A_First : Natural;
      I       : Word64)
     return Boolean
     with
       Pre =>
         A'First <= A_First and then
         A_First <= A'Last and then
         I / 32 <= Word64 (A'Last - A_First),
       Post =>
         Bit_Set'Result =
         ((A (A_First + Natural (I / 32)) and
           2 ** (Natural (I mod 32))) /= 0);

end Foo;
