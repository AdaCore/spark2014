with Ada.Unchecked_Conversion;

procedure Nested_Null with SPARK_Mode is
   type Byte is mod 2 ** 8 with Size => 8;
   type Inner is array (2 .. 0) of Byte with Size => 0;
   type Outer is array (2 .. 0) of Inner
     with Size => 8, Alignment => 1;
   function To_Array is new Ada.Unchecked_Conversion (Byte, Outer);
   function To_Byte is new Ada.Unchecked_Conversion (Outer, Byte);
   X : Outer := To_Array (42);
   Y : Byte := To_Byte (X);
begin
   --  Outer has no scalar components; its eight bits are all padding
   pragma Assert (Y = 0); --@ASSERT:FAIL
end Nested_Null;
