with Interfaces;

use type Interfaces.Unsigned_32;

package Test
is

   type Index is range 0 .. 79;

   subtype Word32 is Interfaces.Unsigned_32;

   type Word32_Array_Type is array (Index range <>) of Word32;

   function XOR2 (V0, V1 : Word32) return Word32
     with Post => XOR2'Result = (V0 xor V1);

   procedure Block_XOR
     (Left   : in     Word32_Array_Type;
      Right  : in     Word32_Array_Type;
      Result :    out Word32_Array_Type)
     with
       Depends =>
         (Result =>+ (Left, Right)),
       Pre =>
         Left'First  = Right'First and
         Left'Last   = Right'Last  and
         Right'First = Result'First and
         Right'Last  = Result'Last,
       Post =>
         (for all I in Index range Left'First .. Left'Last =>
            (Result (I) = XOR2 (Left (I), Right (I))));

end Test;
