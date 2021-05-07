with System; use System;

package Addr is

   type Byte is mod 2 ** 8;

   X : Byte;
   V : Byte with Volatile;

   function F (X : Address) return Address;

   Y : Byte
   with Address => F (X'Address),
        Volatile;

   Z : Byte
   with Address => F (V'Address),
        Volatile;
end Addr;
