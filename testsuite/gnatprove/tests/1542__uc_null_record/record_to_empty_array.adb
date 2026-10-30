with Ada.Unchecked_Conversion;

procedure Record_To_Empty_Array with SPARK_Mode is
   type Byte is mod 2 ** 8 with Size => 8;
   type Bytes is array (1 .. 0) of Byte with Component_Size => 8, Size => 0;
   type Empty is null record with Size => 0;
   function Convert is new Ada.Unchecked_Conversion (Empty, Bytes);
   X : Empty := (null record);
   Y : Bytes := Convert (X);
begin
   pragma Assert (Y'Length = 0);
end Record_To_Empty_Array;
