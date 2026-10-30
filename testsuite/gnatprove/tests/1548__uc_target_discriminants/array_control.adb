with Ada.Unchecked_Conversion;

procedure Array_Control with SPARK_Mode is
   type Word is mod 2 ** 64 with Size => 64;
   type Items is array (1 .. 2) of Natural with Component_Size => 32;
   type Rec is record
      Data : Items;
   end record with Size => 64;
   for Rec use record
      Data at 0 range 0 .. 63;
   end record;
   function To_Array is new Ada.Unchecked_Conversion (Word, Items)
     with Potentially_Invalid;
   function To_Record is new Ada.Unchecked_Conversion (Word, Rec)
     with Potentially_Invalid;
   X : Items := To_Array (0) with Potentially_Invalid;
   Y : Rec := To_Record (0) with Potentially_Invalid;
begin
   pragma Assert (X'First = 1 and X'Last = 2);
   pragma Assert (X'Valid_Scalars);
   pragma Assert (Y'Valid_Scalars);
   pragma Assert (X (1) = 0 and Y.Data (2) = 0);
   pragma Assert (X (1) = 1); --@ASSERT:FAIL
end Array_Control;
