procedure Overlay_Component with SPARK_Mode is
   type Nibble is mod 16 with Size => 4;
   type Other is range -8 .. 7 with Size => 4;
   type Holder is record
      Value : aliased Nibble;
   end record with Size => 8;
   for Holder use record
      Value at 0 range 0 .. 7;
   end record;
   Source : aliased constant Holder := (Value => 8);
   View : constant Other with Import, Address => Source.Value'Address,
     Size => 8, Potentially_Invalid;
begin
   pragma Assert (Source.Value'Size = 8);
   pragma Assert (View'Valid); --@ASSERT:FAIL
   pragma Assert (View = -8); --@ASSERT:FAIL
end Overlay_Component;
