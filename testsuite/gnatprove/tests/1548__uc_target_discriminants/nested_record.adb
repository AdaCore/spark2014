with Ada.Unchecked_Conversion;

procedure Nested_Record with SPARK_Mode is
   type Word is mod 2 ** 64 with Size => 64;
   type Inner (D : Integer) is record
      Value : Natural;
   end record with Size => 64;
   type Outer is record
      Data : Inner (0);
   end record with Size => 64;
   function Convert is new Ada.Unchecked_Conversion (Word, Outer) --@UNCHECKED_CONVERSION:FAIL
     with Potentially_Invalid;
   X : Outer := Convert (0) with Potentially_Invalid;
begin
   pragma Assert (X.Data.Value'Valid); --@ASSERT:FAIL
end Nested_Record;
