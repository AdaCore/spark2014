procedure Overlay_Mutable with SPARK_Mode is
   type Nibble is mod 16 with Size => 4;
   type Byte is mod 256 with Size => 8;
   Source : aliased Nibble := 0 with Size => 8;
   View : Byte with Import,
     Address => Source'Address; --@UNCHECKED_CONVERSION:FAIL
begin
   --  Source is not suitable as a target of arbitrary writes through View.
   --  The suitability check remains even with an uninterpreted view.
   View := 8;
   pragma Assert (View = 8);
   pragma Assert (Source = 8); --@ASSERT:FAIL
   Source := 4;
   pragma Assert (View = 4); --@ASSERT:FAIL
end Overlay_Mutable;
