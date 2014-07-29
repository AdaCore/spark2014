package UnkSize with SPARK_Mode is
   type U8_T  is range 0 .. 2 ** 8 - 1;
   Max_LL_Address_Length : constant := 6;
   subtype LL_Address_Range is U8_T range 1 .. Max_LL_Address_Length;
   type LL_Address is array (LL_Address_Range range <>) of U8_T;
   subtype EA_Range is LL_Address_Range range 1 .. 6;
   subtype EA is LL_Address (EA_Range);
   pragma Suppress (All_Checks);
   v1v : constant Integer := Integer (EA'First);
   v2v : constant Integer := Integer (EA'Last);
   v3v : constant Integer := Integer (EA'Size);
end;
