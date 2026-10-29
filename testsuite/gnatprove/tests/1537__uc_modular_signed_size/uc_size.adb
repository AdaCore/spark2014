with Ada.Unchecked_Conversion;

procedure UC_Size with SPARK_Mode is
   type U24 is mod 2 ** 24 with Size => 24;
   type S24 is range -(2 ** 23) .. 2 ** 23 - 1 with Size => 24;
   function Convert is new Ada.Unchecked_Conversion (U24, S24);
   X : U24 := 16#80_0000#;
   Y : S24 := Convert (X);
begin
   --  The sign bit is bit 23, even though U24 uses BV32 in Why3. The
   --  conversion produces -8388608, so this assertion must not prove.
   pragma Assert (Y >= 0); --@ASSERT:FAIL
end UC_Size;
