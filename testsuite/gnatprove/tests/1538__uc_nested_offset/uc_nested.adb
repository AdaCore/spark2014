with Ada.Unchecked_Conversion;

procedure UC_Nested with SPARK_Mode is
   type Byte is mod 2 ** 8 with Size => 8;
   type Bytes is array (1 .. 2) of Byte with Component_Size => 8;
   type Source is record
      Prefix : Byte;
      Data   : Bytes;
   end record with Size => 24;
   for Source use record
      Prefix at 0 range 0 .. 7;
      Data   at 1 range 0 .. 15;
   end record;
   type Target is new Source;
   function Convert is new Ada.Unchecked_Conversion (Source, Target);
   X : Source := (Prefix => 0, Data => (1, 2));
   Y : Target := Convert (X);
begin
   --  Identical layouts preserve the zero prefix. Array elements must not
   --  contribute bits at the position of the enclosing record's prefix.
   pragma Assert (Y.Prefix = 1); --@ASSERT:FAIL
end UC_Nested;
