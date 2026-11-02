with Ada.Unchecked_Conversion;

procedure Nested_Array with SPARK_Mode is
   type Word is mod 2 ** 64 with Size => 64;
   type Inner (D : Integer) is record
      Value : Natural;
   end record with Size => 64;
   type Items is array (1 .. 1) of Inner (0);
   function Convert is new Ada.Unchecked_Conversion (Word, Items) --@UNCHECKED_CONVERSION:FAIL
     with Potentially_Invalid;
   X : Items := Convert (0) with Potentially_Invalid;
begin
   pragma Assert (X (1).Value'Valid); --@ASSERT:FAIL
end Nested_Array;
