package Pkg1
   with SPARK_Mode
is

    type NvU8  is mod 2 **  8;
    type NvU32 is mod 2 ** 32;


    type Array_T is array (NvU8 range 0 .. 63) of NvU32
       with Size => 2048, Object_Size => 2048;

    procedure Read_Arr(Arr : out Array_T) with
     Relaxed_Initialization => Arr,
     Post => Arr'Initialized;
    procedure Read_Arr2(Arr : out Array_T) with
     Relaxed_Initialization => Arr,
     Post => Arr'Initialized;

end Pkg1;
