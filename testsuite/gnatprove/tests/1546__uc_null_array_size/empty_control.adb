with Ada.Unchecked_Conversion;

procedure Empty_Control with SPARK_Mode is
   type Byte is mod 2 ** 8 with Size => 8;
   type Arr is array (2 .. 0, 2 .. 0) of Byte
     with Size => 0, Alignment => 1;
   type Rec is null record with Size => 0;
   function To_Array is new Ada.Unchecked_Conversion (Rec, Arr);
   function To_Record is new Ada.Unchecked_Conversion (Arr, Rec);
   X : Rec;
   Y : Arr := To_Array (X);
   Z : Rec := To_Record (Y);
begin
   --  These empty representations have no padding
   pragma Assert (Y'Length (1) = 0 and Y'Length (2) = 0);
   pragma Assert (Z = X);
end Empty_Control;
