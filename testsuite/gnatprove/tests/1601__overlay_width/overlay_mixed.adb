procedure Overlay_Mixed with SPARK_Mode is
   type Nibble is mod 16 with Size => 4;
   type Byte is mod 256 with Size => 8;
   type Holder is record
      Value : Byte;
   end record with Size => 8;
   for Holder use record
      Value at 0 range 0 .. 7;
   end record;

   Scalar_Source : aliased constant Nibble := 8 with Size => 8;
   Record_View : constant Holder with Import,
     Address => Scalar_Source'Address;
   Record_Source : aliased constant Holder := (Value => 8);
   Scalar_View : constant Nibble with Import,
     Address => Record_Source'Address, Size => 8, Potentially_Invalid;

   --  Matching scalar widths keep the precise type-based conversion.
   Byte_Source : aliased constant Byte := 8;
   Precise_View : constant Holder with Import, Address => Byte_Source'Address;
begin
   --  These views have no definition because the scalar object is wider
   --  than its type. Their values and validity are not precisely modeled.
   pragma Assert (Record_View.Value = 8); --@ASSERT:FAIL
   pragma Assert (Scalar_View'Valid); --@ASSERT:FAIL
   pragma Assert (Scalar_View = 8); --@ASSERT:FAIL
   pragma Assert (Precise_View.Value = 8);
end Overlay_Mixed;
