with Ada.Unchecked_Conversion;

procedure Widening_Control with SPARK_Mode is
   type U8 is mod 2 ** 8 with Size => 16;
   type Mod_512 is mod 512 with Size => 16;
   function Convert is new Ada.Unchecked_Conversion (U8, Mod_512)
     with Potentially_Invalid;
   Zero : Mod_512 := Convert (0) with Potentially_Invalid;
   Last : Mod_512 := Convert (255) with Potentially_Invalid;
begin
   --  Widen the source to the larger predicate argument without losing bits
   pragma Assert (Zero'Valid and then Zero = 0);
   pragma Assert (Last'Valid and then Last = 255);
end Widening_Control;
