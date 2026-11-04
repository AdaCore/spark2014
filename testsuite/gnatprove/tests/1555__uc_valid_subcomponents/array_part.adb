with Ada.Unchecked_Conversion;

procedure Array_Part with SPARK_Mode is
   type Byte is mod 2 ** 8 with Size => 8;
   type Word is mod 2 ** 32 with Size => 32;
   subtype Small is Natural range 0 .. 127;
   type Bytes is array (1 .. 3) of Byte
     with Component_Size => 8, Size => 24;
   type Target is record
      A : Bytes;
      S : Small;
   end record with Size => 32;
   for Target use record
      A at 0 range 0 .. 23;
      S at 3 range 0 .. 7;
   end record;
   function Convert is new Ada.Unchecked_Conversion (Word, Target)
     with Potentially_Invalid;
   X : Target := Convert (16#0102_0304#) with Potentially_Invalid;
   Y : Target := Convert (16#FF02_0304#) with Potentially_Invalid;
begin
   --  The byte array needs no validity tree, unlike its sibling field.
   pragma Assert (X'Valid_Scalars);
   pragma Assert (X.A = (4, 3, 2) and X.S = 1);
   pragma Assert (not Y.S'Valid);
   pragma Assert (Y.A = (4, 3, 2));
   pragma Assert (X.A (1) = 5); --@ASSERT:FAIL
end Array_Part;
