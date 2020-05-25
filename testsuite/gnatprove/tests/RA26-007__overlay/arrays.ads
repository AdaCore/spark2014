package Arrays with SPARK_Mode is

   type Uint64 is mod 2 ** 64;
   type Uint8 is mod 2 ** 8;
   type Uint32 is mod 2 ** 32;
   type First is array (Uint64 range <>) of Uint8;
   type Second is array (Uint64 range <>) of Uint32;


   Arr_1 : First(0.. 255);
   for Arr_1'Alignment use 4;


   Length : constant Uint64 := arr_1'Length / 4;
   Arr_2 : Second(0 .. Length);
   for Arr_2'Address use arr_1'Address;
   for Arr_2'Alignment use 4;


   Arr_3 : First(0.. 255);
   for Arr_3'Address use Arr_1(0..255)'Address;
   for Arr_3'Alignment use 4;

end Arrays;
