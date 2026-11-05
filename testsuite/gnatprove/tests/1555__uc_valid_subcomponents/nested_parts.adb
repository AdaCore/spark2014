with Ada.Unchecked_Conversion;

procedure Nested_Parts with SPARK_Mode is
   type Byte is mod 2 ** 8 with Size => 8;
   type Word is mod 2 ** 32 with Size => 32;
   subtype Small is Natural range 0 .. 127;
   type Inner is record
      B : Byte;
   end record with Size => 8;
   for Inner use record
      B at 0 range 0 .. 7;
   end record;
   type Pair is array (1 .. 1) of Inner
     with Component_Size => 8, Size => 8;
   type Empty_Record is null record with Size => 0;
   type Item is record
      A : Pair;
      E : Empty_Record;
      S : Small;
   end record with Size => 16;
   for Item use record
      A at 0 range 0 .. 7;
      E at 1 range 0 .. -1;
      S at 1 range 0 .. 7;
   end record;
   type Target is array (1 .. 2) of Item
     with Component_Size => 16, Size => 32;
   function Convert is new Ada.Unchecked_Conversion (Word, Target)
     with Potentially_Invalid;
   X : Target := Convert (16#FF04_0102#) with Potentially_Invalid;
begin
   --  Keep the outer validity tree while skipping the fully valid parts.
   pragma Assert (X (1)'Valid_Scalars);
   pragma Assert (not X (2).S'Valid);
   pragma Assert (X (1).A (1).B = 2 and X (1).S = 1);
   pragma Assert (X (2).A (1).B = 4);
   pragma Assert (X (2).A (1).B = 5); --@ASSERT:FAIL
end Nested_Parts;
