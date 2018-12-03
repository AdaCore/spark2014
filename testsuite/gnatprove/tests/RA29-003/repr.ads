package Repr is

  type Uint64 is mod 2 **64;
  type Uint8 is mod 2 ** 8;

  subtype Index_Type is Uint64 range 0 .. Uint64'Last - 1;

  type My_Arry is array (Index_Type range <>) of Uint8;

  procedure P (A  : in out My_Arry;
                  B  : in My_Arry);

end Repr;
