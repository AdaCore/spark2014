package RFLX.Builtin_Types is

   type Length is new Natural;

   subtype Index is Length range 1 .. Length'Last;

   type Byte is mod 2**8;

   type Bytes is array (Index range <>) of Byte;

   type Bytes_Ptr is access Bytes;

end RFLX.Builtin_Types;
