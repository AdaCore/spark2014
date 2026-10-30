with Ada.Unchecked_Conversion;

procedure Scalar_Boundaries with SPARK_Mode is
   type U24 is mod 2 ** 24 with Size => 24;
   type S24 is range -(2 ** 23) .. 2 ** 23 - 1 with Size => 24;
   function To_Signed is new Ada.Unchecked_Conversion (U24, S24);

   type U32 is mod 2 ** 32 with Size => 32;
   type S32 is range -(2 ** 31) .. 2 ** 31 - 1 with Size => 32;
   function To_Signed is new Ada.Unchecked_Conversion (U32, S32);
begin
   pragma Assert (To_Signed (U24'(0)) = 0);
   pragma Assert (To_Signed (U24'(16#7F_FFFF#)) = S24'Last);
   pragma Assert (To_Signed (U24'(16#80_0000#)) = S24'First);
   pragma Assert (To_Signed (U24'(16#FF_FFFF#)) = -1);

   --  Control cases where the representation size matches the bitvector width
   pragma Assert (To_Signed (U32'(0)) = 0);
   pragma Assert (To_Signed (U32'(16#7FFF_FFFF#)) = S32'Last);
   pragma Assert (To_Signed (U32'(16#8000_0000#)) = S32'First);
   pragma Assert (To_Signed (U32'(16#FFFF_FFFF#)) = -1);
end Scalar_Boundaries;
