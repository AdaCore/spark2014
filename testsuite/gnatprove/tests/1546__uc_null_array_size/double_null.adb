with Ada.Unchecked_Conversion;

procedure Double_Null with SPARK_Mode is
   type Byte is mod 2 ** 8 with Size => 8;
   type Arr is array (2 .. 0, 2 .. 0) of Byte
     with Size => 8, Alignment => 1;
   function To_Array is new Ada.Unchecked_Conversion (Byte, Arr);
   function To_Byte is new Ada.Unchecked_Conversion (Arr, Byte);
   X : Arr := To_Array (42);
   Y : Byte := To_Byte (X);
begin
   --  Both conversions are imprecise because Arr has two dimensions.
   --  Its padding prevents treating them as inverses.
   pragma Assert (Y = 42); --@ASSERT:FAIL
end Double_Null;
