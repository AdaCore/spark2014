with Ada.Unchecked_Conversion;

procedure Composite_Sources (Negative_Record : Boolean) with SPARK_Mode is
   type U24 is mod 2 ** 24 with Size => 24;
   type S24 is range -(2 ** 23) .. 2 ** 23 - 1 with Size => 24;

   type Source_Record is record
      Value : U24;
   end record with Size => 24;
   for Source_Record use record
      Value at 0 range 0 .. 23;
   end record;

   type Source_Array is array (1 .. 1) of U24
     with Component_Size => 24, Size => 24;

   function To_Signed is new Ada.Unchecked_Conversion (Source_Record, S24);
   function To_Signed is new Ada.Unchecked_Conversion (Source_Array, S24);
begin
   --  The scalar target's size determines the sign bit after packing
   pragma Assert (To_Signed (Source_Record'(Value => 0)) = 0);
   pragma Assert
     (To_Signed (Source_Record'(Value => 16#7F_FFFF#)) = S24'Last);
   pragma Assert
     (To_Signed (Source_Record'(Value => 16#80_0000#)) = S24'First);
   pragma Assert (To_Signed (Source_Record'(Value => 16#FF_FFFF#)) = -1);

   pragma Assert (To_Signed (Source_Array'(1 => 0)) = 0);
   pragma Assert
     (To_Signed (Source_Array'(1 => 16#7F_FFFF#)) = S24'Last);
   pragma Assert
     (To_Signed (Source_Array'(1 => 16#80_0000#)) = S24'First);
   pragma Assert (To_Signed (Source_Array'(1 => 16#FF_FFFF#)) = -1);

   --  False assertions must remain unproved for either composite source
   if Negative_Record then
      pragma Assert
        (To_Signed (Source_Record'(Value => 16#80_0000#)) >= 0); --@ASSERT:FAIL
   else
      pragma Assert
        (To_Signed (Source_Array'(1 => 16#80_0000#)) >= 0); --@ASSERT:FAIL
   end if;
end Composite_Sources;
