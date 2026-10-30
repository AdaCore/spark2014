with Ada.Unchecked_Conversion;

procedure Same_Width_Control with SPARK_Mode is
   type U8 is mod 2 ** 8 with Size => 8;
   type Mod_200 is mod 200 with Size => 8;
   function Convert is new Ada.Unchecked_Conversion (U8, Mod_200)
     with Potentially_Invalid;
   Last    : Mod_200 := Convert (199) with Potentially_Invalid;
   Above   : Mod_200 := Convert (200) with Potentially_Invalid;
   Maximum : Mod_200 := Convert (255) with Potentially_Invalid;
begin
   --  Preserve the validity checks when neither bitvector conversion narrows
   pragma Assert (Last'Valid and then Last = 199);
   pragma Assert (not Above'Valid);
   pragma Assert (not Maximum'Valid);
end Same_Width_Control;
