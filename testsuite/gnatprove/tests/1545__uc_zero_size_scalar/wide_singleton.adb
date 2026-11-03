with Ada.Unchecked_Conversion;

procedure Wide_Singleton with SPARK_Mode is
   type Byte is mod 2 ** 8 with Size => 8;
   type E is (A) with Size => 0;
   type Rec is record
      F : E;
   end record with Size => 8;
   for Rec use record
      F at 0 range 0 .. 7;
   end record;
   function Convert is new Ada.Unchecked_Conversion (Byte, Rec)
     with Potentially_Invalid;
   Valid_Rec   : Rec := Convert (0) with Potentially_Invalid;
   Invalid_Rec : Rec := Convert (1) with Potentially_Invalid;
begin
   --  The field occupies eight bits despite the scalar type's zero Size
   pragma Assert (Valid_Rec.F'Valid);
   pragma Assert (Valid_Rec.F = A);
   pragma Assert (not Invalid_Rec.F'Valid);
   pragma Assert (Invalid_Rec.F'Valid); --@ASSERT:FAIL
end Wide_Singleton;
