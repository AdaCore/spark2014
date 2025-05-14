with Ada.Unchecked_Conversion;

procedure B with SPARK_Mode is
   type U8 is mod 2 ** 8 with Size => 8, object_Size => 8;
   type U32 is mod 2 ** 32 with Size => 32, object_Size => 32;

   X : U32 := U32'Last;
   Y : U8 with Import, Size => 32, Address => X'Address;

begin
   pragma Assert (Y'Valid); --  fails at runtime
end B;
