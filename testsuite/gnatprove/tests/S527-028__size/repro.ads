package Repro with SPARK_Mode is

   type NvU32 is mod 2**32;

   type Type1 is record
      X, Y : NvU32;
   end record
     with Size => 64, Object_Size => 64;

   type Arr is array (NvU32 range <>) of NvU32;
   subtype Arr_Type1 is Arr (0 .. Type1'Size / NvU32'Size - 1);

   pragma Assert (Arr_Type1'Size = Type1'Size);  --  @ASSERT:PASS

end Repro;
