with Ada.Unchecked_Conversion;

procedure Array_Target with SPARK_Mode is
   type U32 is mod 2 ** 32 with Size => 32;
   type U8 is mod 2 ** 8 with Size => 8;
   type Target is array (1 .. 2) of U8
     with Component_Size => 16, Size => 32;
   function Convert is new Ada.Unchecked_Conversion (U32, Target)
     with Potentially_Invalid;
   X_Valid   : U32 := 16#00FF_00FF#;
   X_Invalid : U32 := 16#0100_0100#;
   Y_Valid   : Target := Convert (X_Valid) with Potentially_Invalid;
   Y_Invalid : Target := Convert (X_Invalid) with Potentially_Invalid;
begin
   pragma Assert (Y_Valid'Valid_Scalars);
   pragma Assert (Y_Valid (1) = 255 and Y_Valid (2) = 255);
   --  Both components contain an invalid 16-bit pattern
   pragma Assert
     (Y_Invalid (1)'Valid and Y_Invalid (2)'Valid); --@ASSERT:FAIL
end Array_Target;
