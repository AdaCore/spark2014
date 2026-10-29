with Ada.Unchecked_Conversion;

procedure Validity_Boundaries with SPARK_Mode is
   type U16 is mod 2 ** 16 with Size => 16;
   type U8 is mod 2 ** 8 with Size => 16;
   function Convert is new Ada.Unchecked_Conversion (U16, U8)
     with Potentially_Invalid;
   Zero    : U8 := Convert (0) with Potentially_Invalid;
   Last    : U8 := Convert (255) with Potentially_Invalid;
   Above   : U8 := Convert (256) with Potentially_Invalid;
   Maximum : U8 := Convert (16#FFFF#) with Potentially_Invalid;
begin
   pragma Assert (Zero'Valid and then Zero = 0);
   pragma Assert (Last'Valid and then Last = 255);
   pragma Assert (not Above'Valid);
   pragma Assert (not Maximum'Valid);
end Validity_Boundaries;
