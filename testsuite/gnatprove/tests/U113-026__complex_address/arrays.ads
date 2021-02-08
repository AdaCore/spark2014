with System;
package Arrays with SPARK_Mode is

   type Uint64 is mod 2 ** 64;
   type Uint8 is mod 2 ** 8;
   type Uint32 is mod 2 ** 32;
   type First is array (Uint64 range <>) of Uint8;
   type Second is array (Uint64 range <>) of Uint32;


   Arr_1 : First(0.. 255);
   for Arr_1'Alignment use 4;


   Length : constant Uint64 := arr_1'Length / 4;
   Arr_2 : Second(0 .. Length) with Volatile;
   for Arr_2'Address use arr_1'Address;
   for Arr_2'Alignment use 4;

   function F (X : System.Address) return System.Address;
   function G (X : System.Address) return Boolean;

   Arr_3 : First(0.. 255) with Volatile;
   for Arr_3'Alignment use 4;
   for Arr_3'Address use F (Arr_1(0..255)'Address);

   Arr_4 : First(0 .. 255);
   for Arr_4'Address use (if (for all I in Uint64 range 0 .. 1 => G (Arr_3 (I)'Address)) then Arr_2'Address else Arr_3'Address);


   Arr_5 : First(0 .. 255);
   for Arr_5'Address use (Arr_3((if G (Arr_3'Address) then 0 else 1) .. 255)'Address);

   Arr_6 : First(0 .. 255);
   for Arr_6'Address use (First'(Arr_3((if G (Arr_3'Address) then 0 else 1) .. 255))(1 .. 255)'Address);
end Arrays;
