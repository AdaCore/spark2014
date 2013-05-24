package body Arrays
is
   type Unsigned_Byte is range 0..255;
   type Bool_Map is array (Boolean) of Unsigned_Byte;

   procedure Test_L (A : in Bool_Map)
   is
   begin
      pragma Assert (for some B in Boolean => (A (B) > 0));
      null;
   end Test_L;
end Arrays;
