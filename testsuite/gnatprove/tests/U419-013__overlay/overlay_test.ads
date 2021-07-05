package Overlay_Test is
   type NvU32 is mod 2**32;
   type NvU8 is mod 2**8;

   type Nv_DW_Block64 is array (NvU32 range 0 .. 1) of NvU32 with
      Size        => 64,
      Object_Size => 64;
   type Nv_B_Block64 is array (NvU32 range 0 .. 7) of NvU8 with
      Size        => 64,
      Object_Size => 64;

   procedure Test_Program (A : aliased Nv_DW_Block64) with Global => null;
end Overlay_Test;
