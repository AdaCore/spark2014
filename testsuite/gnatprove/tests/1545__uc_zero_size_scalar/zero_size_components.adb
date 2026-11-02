with Ada.Unchecked_Conversion;

procedure Zero_Size_Components with SPARK_Mode is
   type Byte is mod 2 ** 8 with Size => 8;
   type Word is mod 2 ** 16 with Size => 16;
   type E is (A) with Size => 0;
   type Rec is record
      Tag   : E;
      Value : Byte;
   end record with Size => 8;
   for Rec use record
      Tag   at 0 range 0 .. -1;
      Value at 0 range 0 .. 7;
   end record;
   type Arr is array (1 .. 2) of Rec
     with Component_Size => 8, Size => 16, Alignment => 2;
   function To_Word is new Ada.Unchecked_Conversion (Arr, Word);
   function To_Array is new Ada.Unchecked_Conversion (Word, Arr);
   X : Arr := (others => (Tag => A, Value => 42));
   Y : Word := To_Word (X);
   Z : Arr := To_Array (Y);
begin
   pragma Assert (Y = 16#2A2A#);
   pragma Assert (Z (1).Tag = A);
   pragma Assert (Z (2).Tag = A);
   pragma Assert (Z (1).Value = 42);
   pragma Assert (Z (2).Value = 42);
   pragma Assert (Z = X);
   pragma Assert (Y /= 16#2A2A#); --@ASSERT:FAIL
end Zero_Size_Components;
