package Array_Cntx with SPARK_Mode is

   type U64 is mod 2 ** 64;

   type Too_Big_Array is array (U64 range <>) of Natural;

   V1 : Too_Big_Array (0 .. 2 ** 64 - 2) := (2 ** 64-2 => 1, others => 0);
   V2 : Too_Big_Array (0 .. 2 ** 64 - 1) := (2 ** 64-2 => 1, others => 0);

   pragma Assert (V1 > V2); --@ASSERT:FAIL

end Array_Cntx;
