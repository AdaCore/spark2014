with Ada.Unchecked_Conversion;
with Interfaces; use Interfaces;

procedure Modular_Subtypes with SPARK_Mode is
   type Word is mod 2 ** 24 with Size => 32;
   subtype Small_Word is Word range 0 .. 255;

   function Convert is new Ada.Unchecked_Conversion (Word, Unsigned_32);
   function Convert_Small is new
     Ada.Unchecked_Conversion (Small_Word, Unsigned_8);

   X : Word := 42;
   Y : Small_Word := 17;
begin
   pragma Assert (Convert (X) = 42); -- @ASSERT:PASS
   pragma Assert (Convert_Small (Y) = 17); -- @ASSERT:PASS
end Modular_Subtypes;
