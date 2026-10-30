with Ada.Unchecked_Conversion;

procedure Biased_Enum_Array with SPARK_Mode is
   type Byte is mod 2 ** 8 with Size => 8;
   type E is (A, B, C);
   subtype Last_Two is E range B .. C;
   type Arr is array (1 .. 8) of Last_Two
     with Component_Size => 1, Size => 8;
   function Convert is new Ada.Unchecked_Conversion (Arr, Byte);
   X : Arr := (others => B);
   Y : Byte := Convert (X);
begin
   --  The component size clause introduces a biased enumeration subtype.
   --  Each component stores zero for B.
   pragma Assert (Y = 255); --@ASSERT:FAIL
end Biased_Enum_Array;
