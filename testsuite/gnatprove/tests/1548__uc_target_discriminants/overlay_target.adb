procedure Overlay_Target with SPARK_Mode is
   type Word is mod 2 ** 64 with Size => 64;
   type Rec (D : Integer) is record
      Value : Natural;
   end record with Size => 64;
   subtype Fixed is Rec (0);
   Source : constant Word := 0;
   X : constant Fixed with Import, Address => Source'Address, --@UNCHECKED_CONVERSION:FAIL
     Potentially_Invalid;
begin
   pragma Assert (X.Value'Valid); --@ASSERT:FAIL
end Overlay_Target;
