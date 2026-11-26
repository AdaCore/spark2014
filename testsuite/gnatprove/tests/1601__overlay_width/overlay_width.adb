with Ada.Unchecked_Conversion;

procedure Overlay_Width with SPARK_Mode is
   type Nibble is mod 16 with Size => 4;
   type Other is range -8 .. 7 with Size => 4;
   function Convert is new Ada.Unchecked_Conversion (Nibble, Other);
   Source : aliased constant Nibble := 8 with Size => 8;
   View : constant Other with Import, Address => Source'Address, Size => 8,
     Potentially_Invalid;

   procedure Check_View with Pre => True;

   procedure Check_View is
   begin
      --  No defining axiom should supply a value or validity in this scope.
      pragma Assert (View'Valid); --@ASSERT:FAIL
      pragma Assert (View = -8); --@ASSERT:FAIL
   end Check_View;
begin
   pragma Assert (Source'Size = 8 and View'Size = 8);
   pragma Assert (Nibble'Size = 4 and Other'Size = 4);
   --  The ordinary UC still interprets a four-bit representation.
   pragma Assert (Convert (Source) = -8);
   --  The overlay reads an eight-bit representation of +8, outside Other.
   pragma Assert (View'Valid); --@ASSERT:FAIL
   pragma Assert (View = -8); --@ASSERT:FAIL
   Check_View;
end Overlay_Width;
