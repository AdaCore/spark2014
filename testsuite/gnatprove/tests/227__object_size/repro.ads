package Repro is
   type uint8_t is mod 2**8 with Size => 8;
   type UnconstrainedGpuIdArray is array (Natural range <>) of Uint8_T;
   subtype GpuIdArray is UnconstrainedGpuIdArray(0 .. 15)
     with Object_size => uint8_t'Object_size * 16;
   function GetObjectSize return Integer is (GpuIdArray'Object_size);

    type ByteArray16 is array (Natural range 0 .. 15) of uint8_t;
    type NvSciRmGpuId is record
        bytes : ByteArray16;
    end record
    with Convention => C_Pass_By_Copy,
        Object_size => uint8_t'Object_size * 16;
    function GetObjectSize2 return Integer is (NvSciRmGpuId'Object_size);
end Repro;
