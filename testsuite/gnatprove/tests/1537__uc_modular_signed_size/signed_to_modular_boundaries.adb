with Ada.Unchecked_Conversion;

procedure Signed_To_Modular_Boundaries with SPARK_Mode is
   type S24 is range -(2 ** 23) .. 2 ** 23 - 1 with Size => 24;
   type U24 is mod 2 ** 24 with Size => 24;
   function Convert is new Ada.Unchecked_Conversion (S24, U24);

   type S32 is range -(2 ** 31) .. 2 ** 31 - 1 with Size => 32;
   type U32 is mod 2 ** 32 with Size => 32;
   function Convert is new Ada.Unchecked_Conversion (S32, U32);
begin
   pragma Assert (Convert (S24'(0)) = 0);
   pragma Assert (Convert (S24'(S24'Last)) = 16#7F_FFFF#);
   pragma Assert (Convert (S24'(S24'First)) = 16#80_0000#);
   pragma Assert (Convert (S24'(-1)) = 16#FF_FFFF#);

   --  Control cases with matching representation and bitvector widths
   pragma Assert (Convert (S32'(0)) = 0);
   pragma Assert (Convert (S32'(S32'Last)) = 16#7FFF_FFFF#);
   pragma Assert (Convert (S32'(S32'First)) = 16#8000_0000#);
   pragma Assert (Convert (S32'(-1)) = 16#FFFF_FFFF#);
end Signed_To_Modular_Boundaries;
