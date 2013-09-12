with System;
package P is
   type Base is range 1 .. 10;
   type Int is new Base;

   CPU_SETSIZE : constant := 1_024;
   type bit_field is array (1 .. CPU_SETSIZE) of Boolean;
   for bit_field'Size use CPU_SETSIZE;
   pragma Pack (bit_field);
   pragma Convention (C, bit_field);
end;
