package Arrays with SPARK_Mode is

   type Uint64 is mod 2 ** 64;
   type Uint8 is mod 2 ** 8;
   type Uint32 is mod 2 ** 32;
   type First is array (Uint64 range <>) of Uint8;
   type Second is array (Uint64 range <>) of Uint32;


   Arr_1 : First(0.. 255);


   Length : constant Uint64 := arr_1'Length / 4;
   Arr_2 : Second(0 .. Length);
   for Arr_2'Address use arr_1'Address;
end Arrays;
