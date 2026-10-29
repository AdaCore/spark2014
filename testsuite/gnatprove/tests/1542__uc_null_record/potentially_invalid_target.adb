with Ada.Unchecked_Conversion;

procedure Potentially_Invalid_Target with SPARK_Mode is
   type Byte is mod 2 ** 8 with Size => 8;
   type Empty is null record with Size => 0;
   type Kind is (First, Second, Third) with Size => 8;
   type Target is record
      Value   : Kind;
      Nothing : Empty;
   end record with Size => 8, Alignment => 1;
   for Target use record
      Value   at 0 range 0 .. 7;
      Nothing at 1 range 0 .. -1;
   end record;

   function Convert is new Ada.Unchecked_Conversion (Byte, Target)
     with Potentially_Invalid;

   Valid   : constant Target := Convert (1) with Potentially_Invalid;
   Invalid : constant Target := Convert (3) with Potentially_Invalid;
begin
   pragma Assert (Valid'Valid_Scalars);
   pragma Assert (Valid.Value = Second);
   pragma Assert (Valid.Nothing = (null record));
   pragma Assert (not Invalid'Valid_Scalars);
   pragma Assert (Invalid'Valid_Scalars); --@ASSERT:FAIL
end Potentially_Invalid_Target;
